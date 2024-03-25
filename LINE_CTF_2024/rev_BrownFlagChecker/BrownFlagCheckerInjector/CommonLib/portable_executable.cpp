#include"portable_executable.hpp"

#pragma warning(push)
#pragma warning(disable:4091)
#include<ImageHlp.h>	// 無名enumへのtypedefが含まれている
#pragma warning(pop)
#pragma comment(lib, "Dbghelp.lib")

namespace utils
{
	portable_executable::portable_executable(const fs::path& filepath) :
		contentType_(content_type::file)
	{
		// http://stackoverflow.com/questions/2975639/resolving-rvas-for-import-and-export-tables-within-a-pe-file
		this->hFile_.reset(CreateFileW(
			filepath.c_str(),
			GENERIC_READ,
			FILE_SHARE_READ,
			nullptr,
			OPEN_EXISTING,
			FILE_ATTRIBUTE_NORMAL,
			nullptr));
		if (this->hFile_.get() == INVALID_HANDLE_VALUE)
		{
			throw utils::wide_exception(filepath.native() + L" を開けませんでした: " + utils::get_last_error_message_as_unicode());
		}

		this->hFileMappingObject_.reset(::CreateFileMappingW(
			this->hFile_.get(),
			nullptr,
			PAGE_READONLY,	// SEC_IMAGE や SEC_IMAGE_NO_EXECUTE ってのもあるけど何だろうこれ
			0,
			0,
			nullptr));
		if (this->hFileMappingObject_.get() == nullptr)
		{
			throw utils::wide_exception(L"ファイルマッピングの作成に失敗しました:" + utils::get_last_error_message_as_unicode());
		}

		this->pMappedAddress_.reset(::MapViewOfFile(
			this->hFileMappingObject_.get(),
			FILE_MAP_READ,
			0,
			0,
			0));
		if (this->pMappedAddress_.get() == nullptr)
		{
			throw utils::wide_exception(L"ファイルマッピングからのアドレス取得に失敗しました: " + utils::get_last_error_message_as_unicode());
		}
	}
	portable_executable::portable_executable(HMODULE hModule) :
		contentType_(content_type::image),
		hModule_(hModule)
	{
	}
	BYTE* portable_executable::get_base_address() noexcept
	{
		switch (this->contentType_)
		{
		case content_type::file:
			return static_cast<BYTE*>(this->pMappedAddress_.get());
		case content_type::image:
			return reinterpret_cast<BYTE*>(this->hModule_);
		default:
			return nullptr;
		}
	}
	bool portable_executable::is_mapped_as_image() const noexcept
	{
		return (this->contentType_ == content_type::image);
	}
	IMAGE_IMPORT_DESCRIPTOR* portable_executable::get_directory_entry_import()
	{
		auto baseAddress = this->get_base_address();
		if (baseAddress == 0) { return nullptr; }

		ULONG imageSize;
		return static_cast<IMAGE_IMPORT_DESCRIPTOR*>(::ImageDirectoryEntryToDataEx(
			baseAddress,
			this->is_mapped_as_image(),
			IMAGE_DIRECTORY_ENTRY_IMPORT,
			&imageSize,
			nullptr));
	}

	void* portable_executable::get_address_from_rva_impl(ULONGLONG rva)
	{
		auto pBaseAddress = this->get_base_address();
		switch (this->contentType_)
		{
		case content_type::file:
			return ::ImageRvaToVa(
				::ImageNtHeader(pBaseAddress),
				pBaseAddress,
				static_cast<ULONG>(rva), // DbgHelp側がULONGLONG未対応なので仕方なくキャスト、RVAなので多分そこまで大きくはならないはず
				nullptr);
		case content_type::image:
			return pBaseAddress + rva;
		}
		return nullptr;
	}

	void* hook_api_impl(portable_executable& imagePE, portable_executable& filePE, const char* apiName, void* hookFunc)
	{
		if (!imagePE.is_mapped_as_image() || filePE.is_mapped_as_image()) { return nullptr; }

		// http://qiita.com/kobake@github/items/8d3d3637c7af0b270098
		// https://github.com/kobake/ApiHookSample/blob/master/src/rewrite.cpp
		// http://hp.vector.co.jp/authors/VA050396/tech_07.html 「インポートネームテーブルは存在しなくても問題ありませんが、バインドはできなくなってしまいます。Borland 製の古いリンカはこのインポートネームテーブルを生成しません。」

		auto pImageDesc = imagePE.get_directory_entry_import();
		if (pImageDesc == nullptr) { return nullptr; }

		auto pFileImageDesc = filePE.get_directory_entry_import();
		if (pFileImageDesc == nullptr) { return nullptr; }

		// http://hp.vector.co.jp/authors/VA050396/tech_08.html 「エクスポートの転送を使ったりすることで IAT には同じインポートシンボルが複数存在する可能性があるので、書き換えたとしてもループは抜けません。」
		void* result = nullptr;

		// 「Characteristicsメンバーが0なら終端」なコメントがあるが、共用体メンバーであるOriginalFirstThunkはINTが無ければ0になるので、それらは終了判定には使えない
		for (; pImageDesc->FirstThunk && pFileImageDesc->FirstThunk; ++pImageDesc, ++pFileImageDesc) {
			auto pFirstThunk = imagePE.get_address_from_rva<IMAGE_THUNK_DATA*>(pImageDesc->FirstThunk);
			auto pFileFirstThunk = filePE.get_address_from_rva<IMAGE_THUNK_DATA*>(pFileImageDesc->FirstThunk);

			// 関数列挙
			for (; pFirstThunk->u1.Function; ++pFirstThunk, ++pFileFirstThunk) {
				if (IMAGE_SNAP_BY_ORDINAL(pFileFirstThunk->u1.Ordinal)) { continue; }

				auto pImportName = filePE.get_address_from_rva<IMAGE_IMPORT_BY_NAME*>(pFileFirstThunk->u1.AddressOfData);
				if (lstrcmpA(pImportName->Name, apiName) != 0) { continue; }

				// 保護状態変更
				DWORD oldProtect = 0;
				if (VirtualProtect(&pFirstThunk->u1.Function, sizeof(pFirstThunk->u1.Function), PAGE_READWRITE, &oldProtect)) {
					// 書き換え
					auto pOrgFunc = reinterpret_cast<void*>(pFirstThunk->u1.Function); // 元のアドレスを保存しておく
					WriteProcessMemory(GetCurrentProcess(), &pFirstThunk->u1.Function, &hookFunc, sizeof(pFirstThunk->u1.Function), nullptr);
					pFirstThunk->u1.Function = reinterpret_cast<DWORD_PTR>(hookFunc);

					// 保護状態戻し
					VirtualProtect(&pFirstThunk->u1.Function, sizeof(pFirstThunk->u1.Function), oldProtect, &oldProtect);

					result = pOrgFunc;	// 元々のアドレスを保存
				}
			}
		}

		return result;
	}
}
