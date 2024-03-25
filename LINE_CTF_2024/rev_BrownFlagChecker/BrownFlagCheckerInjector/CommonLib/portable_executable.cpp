#include"portable_executable.hpp"

#pragma warning(push)
#pragma warning(disable:4091)
#include<ImageHlp.h>	// ����enum�ւ�typedef���܂܂�Ă���
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
			throw utils::wide_exception(filepath.native() + L" ���J���܂���ł���: " + utils::get_last_error_message_as_unicode());
		}

		this->hFileMappingObject_.reset(::CreateFileMappingW(
			this->hFile_.get(),
			nullptr,
			PAGE_READONLY,	// SEC_IMAGE �� SEC_IMAGE_NO_EXECUTE ���Ă̂����邯�ǉ����낤����
			0,
			0,
			nullptr));
		if (this->hFileMappingObject_.get() == nullptr)
		{
			throw utils::wide_exception(L"�t�@�C���}�b�s���O�̍쐬�Ɏ��s���܂���:" + utils::get_last_error_message_as_unicode());
		}

		this->pMappedAddress_.reset(::MapViewOfFile(
			this->hFileMappingObject_.get(),
			FILE_MAP_READ,
			0,
			0,
			0));
		if (this->pMappedAddress_.get() == nullptr)
		{
			throw utils::wide_exception(L"�t�@�C���}�b�s���O����̃A�h���X�擾�Ɏ��s���܂���: " + utils::get_last_error_message_as_unicode());
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
				static_cast<ULONG>(rva), // DbgHelp����ULONGLONG���Ή��Ȃ̂Ŏd���Ȃ��L���X�g�ARVA�Ȃ̂ő��������܂ő傫���͂Ȃ�Ȃ��͂�
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
		// http://hp.vector.co.jp/authors/VA050396/tech_07.html �u�C���|�[�g�l�[���e�[�u���͑��݂��Ȃ��Ă���肠��܂��񂪁A�o�C���h�͂ł��Ȃ��Ȃ��Ă��܂��܂��BBorland ���̌Â������J�͂��̃C���|�[�g�l�[���e�[�u���𐶐����܂���B�v

		auto pImageDesc = imagePE.get_directory_entry_import();
		if (pImageDesc == nullptr) { return nullptr; }

		auto pFileImageDesc = filePE.get_directory_entry_import();
		if (pFileImageDesc == nullptr) { return nullptr; }

		// http://hp.vector.co.jp/authors/VA050396/tech_08.html �u�G�N�X�|�[�g�̓]�����g�����肷�邱�Ƃ� IAT �ɂ͓����C���|�[�g�V���{�����������݂���\��������̂ŁA�����������Ƃ��Ă����[�v�͔����܂���B�v
		void* result = nullptr;

		// �uCharacteristics�����o�[��0�Ȃ�I�[�v�ȃR�����g�����邪�A���p�̃����o�[�ł���OriginalFirstThunk��INT���������0�ɂȂ�̂ŁA�����͏I������ɂ͎g���Ȃ�
		for (; pImageDesc->FirstThunk && pFileImageDesc->FirstThunk; ++pImageDesc, ++pFileImageDesc) {
			auto pFirstThunk = imagePE.get_address_from_rva<IMAGE_THUNK_DATA*>(pImageDesc->FirstThunk);
			auto pFileFirstThunk = filePE.get_address_from_rva<IMAGE_THUNK_DATA*>(pFileImageDesc->FirstThunk);

			// �֐���
			for (; pFirstThunk->u1.Function; ++pFirstThunk, ++pFileFirstThunk) {
				if (IMAGE_SNAP_BY_ORDINAL(pFileFirstThunk->u1.Ordinal)) { continue; }

				auto pImportName = filePE.get_address_from_rva<IMAGE_IMPORT_BY_NAME*>(pFileFirstThunk->u1.AddressOfData);
				if (lstrcmpA(pImportName->Name, apiName) != 0) { continue; }

				// �ی��ԕύX
				DWORD oldProtect = 0;
				if (VirtualProtect(&pFirstThunk->u1.Function, sizeof(pFirstThunk->u1.Function), PAGE_READWRITE, &oldProtect)) {
					// ��������
					auto pOrgFunc = reinterpret_cast<void*>(pFirstThunk->u1.Function); // ���̃A�h���X��ۑ����Ă���
					WriteProcessMemory(GetCurrentProcess(), &pFirstThunk->u1.Function, &hookFunc, sizeof(pFirstThunk->u1.Function), nullptr);
					pFirstThunk->u1.Function = reinterpret_cast<DWORD_PTR>(hookFunc);

					// �ی��Ԗ߂�
					VirtualProtect(&pFirstThunk->u1.Function, sizeof(pFirstThunk->u1.Function), oldProtect, &oldProtect);

					result = pOrgFunc;	// ���X�̃A�h���X��ۑ�
				}
			}
		}

		return result;
	}
}
