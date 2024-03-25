#pragma once

#include<type_traits>
#include<string>
#include<string_view>
#include<mutex>
#include<filesystem>

#define NOMINMAX
#define WIN32_LEAN_AND_MEAN
#define STRICT
#include<Windows.h>

namespace fs = std::filesystem;

namespace utils
{
	class wide_exception : public std::exception
	{
		std::wstring wide_what_;
	public:
		wide_exception(const std::wstring& wide_what) : wide_what_(wide_what) {}
		virtual char const* what() const override { return "use wide_what()"; }
		virtual const wchar_t* wide_what() const { return this->wide_what_.c_str(); }
	};

	// �|�C���^���const�C���q���������܂��B
	template<class T>
	constexpr auto remove_const_of_pointer_cast(T x) noexcept
	{
		static_assert(std::is_pointer_v<T>);

		return const_cast<std::add_pointer_t<std::remove_const_t<std::remove_pointer_t<T>>>>(x);
	}

	// �^����T���֐��|�C���^���ǂ������擾���܂��B
	// http://stackoverflow.com/questions/6560590/is-function-pointer-for-type-traits
	template<class T>
	constexpr bool is_function_pointer_v = std::is_pointer_v<T> && std::is_function_v<std::remove_pointer_t<T>>;

	// std::unique_lock<T>���쐬����w���p�[�֐��ł��B
	// http://d.hatena.ne.jp/gintenlabo/20110628/1309221610
	template< class Mutex, class... Args >
	inline std::unique_lock<Mutex> make_unique_lock(Mutex& m, Args&&... args)
	{
		return std::unique_lock<Mutex>(m, std::forward<Args>(args)...);
	}

	// ANSI�������Unicode������ɕϊ����܂��B
	std::wstring ansi_to_unicode(const char* ansiStr);

	// GetLastError()�̓��e��Unicode������Ŏ擾���܂��B
	std::wstring get_last_error_message_as_unicode();

	// �v���Z�X�����s���Ă���EXE�t�@�C���̃t���p�X���擾���܂��B
	fs::path get_current_exe_path();

	// �K�v�ȏꍇ�Astd::wcout�ŏo�͉\�Ȍ`���ɕϊ����܂��B
	template<class T>
	constexpr auto to_outputable(const T& x) noexcept { return x; }
	inline auto to_outputable(const char* str) { return utils::ansi_to_unicode(str); }	// ��ASCII���܂�char*��wcout�ɗ����Ɠǂݍ��݈ᔽ����������̂�wchar_t*�ɕϊ�����

	// �������J���}��؂�ŏo�͂��܂��B
	inline void dump_parameters(std::wostream& out) {}	// �ċA�I��
	template<class Head, class... Tail>
	void dump_parameters(std::wostream& out, const Head &head, const Tail&... tail)
	{
		out << L", " << utils::to_outputable(head);
		utils::dump_parameters(out, tail...);
	}

	inline void dump_named_parameters(std::wostream& out) {}	// �ċA�I��
	template<class HeadValue, class... Tail>
	void dump_named_parameters(std::wostream&out, const std::wstring_view& name, const HeadValue& headValue, const Tail&... tail)
	{
		out << L", " << name << L": " << utils::to_outputable(headValue);
		utils::dump_named_parameters(out, tail...);
	}

	// unique_ptr��deleter�p�֐��I�u�W�F�N�g
	struct close_handle_deleter
	{
		typedef HANDLE pointer;
		void operator() (HANDLE handle) const
		{
			if (handle != nullptr && handle != INVALID_HANDLE_VALUE)
			{
				::CloseHandle(handle);
			}
		}
	};
	struct unmap_view_of_file_deleter
	{
		typedef LPVOID pointer;
		void operator() (LPVOID pBaseAddress) const
		{
			if (pBaseAddress != nullptr)
			{
				::UnmapViewOfFile(pBaseAddress);
			}
		}
	};
	struct process_information_deleter
	{
		void operator() (PROCESS_INFORMATION* p) const
		{
			if (p != nullptr)
			{
				if (p->hProcess != nullptr) { ::CloseHandle(p->hProcess); }
				if (p->hThread != nullptr) { ::CloseHandle(p->hThread); }
				delete p;
			}
		}
	};
}
