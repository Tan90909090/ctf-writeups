#pragma once

#include"utils.hpp"

namespace utils
{
	// PE�t�H�[�}�b�g�̃t�@�C���������܂��B
	class portable_executable
	{
	public:
		// �w��p�X�̎��s�t�@�C����ێ����܂��B
		explicit portable_executable(const fs::path& filepath);
		// �w�胂�W���[���̃C���[�W��ێ����܂��B
		explicit portable_executable(HMODULE hModule);

		~portable_executable() = default;
		portable_executable(const portable_executable&) = delete;
		portable_executable& operator =(const portable_executable&) = delete;

		// �x�[�X�A�h���X���擾���܂��B���s�����ꍇ��nullptr�ł��B
		BYTE* get_base_address() noexcept;
		bool is_mapped_as_image() const noexcept;
		// PE�t�@�C����IMPORT�Z�N�V�������擾���܂��B���݂��Ȃ��ꍇ��nullptr�ł��B
		IMAGE_IMPORT_DESCRIPTOR* get_directory_entry_import();

		// RVA(Relatinal Virtual Address)�����Ɏ��ۂ̃A�h���X���擾���܂��B
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

	// imagePE��IAT�ɂ���w��API���A�w�肳�ꂽ�A�h���X�ɒu�������܂��B
	// ���������ꍇ�͌��X��API�̃A�h���X���A�����łȂ��ꍇ��nullptr��Ԃ��܂��B
	// imagePE��INT�������ꍇ�ɔ�����filePE���g�p���܂�
	template<class T>
	T hook_api(portable_executable& imagePE, portable_executable& filePE, const char* apiName, T hookFunc)
	{
		static_assert(utils::is_function_pointer_v<T>);

		return static_cast<T>(utils::hook_api_impl(imagePE, filePE, apiName, hookFunc));
	}
}
