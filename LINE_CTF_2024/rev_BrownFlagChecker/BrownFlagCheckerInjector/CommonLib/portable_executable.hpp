#pragma once

#include"utils.hpp"

namespace utils
{
	// PEフォーマットのファイルを扱います。
	class portable_executable
	{
	public:
		// 指定パスの実行ファイルを保持します。
		explicit portable_executable(const fs::path& filepath);
		// 指定モジュールのイメージを保持します。
		explicit portable_executable(HMODULE hModule);

		~portable_executable() = default;
		portable_executable(const portable_executable&) = delete;
		portable_executable& operator =(const portable_executable&) = delete;

		// ベースアドレスを取得します。失敗した場合はnullptrです。
		BYTE* get_base_address() noexcept;
		bool is_mapped_as_image() const noexcept;
		// PEファイルのIMPORTセクションを取得します。存在しない場合はnullptrです。
		IMAGE_IMPORT_DESCRIPTOR* get_directory_entry_import();

		// RVA(Relatinal Virtual Address)を元に実際のアドレスを取得します。
		template<class T>
		T get_address_from_rva(ULONGLONG rva)
		{
			static_assert(std::is_pointer_v<T>);
			return static_cast<T>(this->get_address_from_rva_impl(rva));
		}

	private:

		void* get_address_from_rva_impl(ULONGLONG rva);

		enum class content_type
		{
			file,
			image,
		};
		content_type contentType_ = content_type::file;
		std::unique_ptr<HANDLE, utils::close_handle_deleter> hFile_;
		std::unique_ptr<HANDLE, utils::close_handle_deleter> hFileMappingObject_;
		std::unique_ptr<LPVOID, utils::unmap_view_of_file_deleter> pMappedAddress_;
		HMODULE hModule_ = nullptr;
	};

	void* hook_api_impl(portable_executable& imagePE, portable_executable& filePE, const char* apiName, void* hookFunc);

	// imagePEのIATにある指定APIを、指定されたアドレスに置き換えます。
	// 成功した場合は元々のAPIのアドレスを、そうでない場合はnullptrを返します。
	// imagePEにINTが無い場合に備えてfilePEを使用します
	template<class T>
	T hook_api(portable_executable& imagePE, portable_executable& filePE, const char* apiName, T hookFunc)
	{
		static_assert(utils::is_function_pointer_v<T>);

		return static_cast<T>(utils::hook_api_impl(imagePE, filePE, apiName, hookFunc));
	}
}
