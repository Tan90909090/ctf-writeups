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

	// ポインタ先のconst修飾子を除去します。
	template<class T>
	constexpr auto remove_const_of_pointer_cast(T x) noexcept
	{
		static_assert(std::is_pointer_v<T>);

		return const_cast<std::add_pointer_t<std::remove_const_t<std::remove_pointer_t<T>>>>(x);
	}

	// 型引数Tが関数ポインタかどうかを取得します。
	// http://stackoverflow.com/questions/6560590/is-function-pointer-for-type-traits
	template<class T>
	constexpr bool is_function_pointer_v = std::is_pointer_v<T> && std::is_function_v<std::remove_pointer_t<T>>;

	// std::unique_lock<T>を作成するヘルパー関数です。
	// http://d.hatena.ne.jp/gintenlabo/20110628/1309221610
	template< class Mutex, class... Args >
	inline std::unique_lock<Mutex> make_unique_lock(Mutex& m, Args&&... args)
	{
		return std::unique_lock<Mutex>(m, std::forward<Args>(args)...);
	}

	// ANSI文字列をUnicode文字列に変換します。
	std::wstring ansi_to_unicode(const char* ansiStr);

	// GetLastError()の内容をUnicode文字列で取得します。
	std::wstring get_last_error_message_as_unicode();

	// プロセスを実行しているEXEファイルのフルパスを取得します。
	fs::path get_current_exe_path();

	// 必要な場合、std::wcoutで出力可能な形式に変換します。
	template<class T>
	constexpr auto to_outputable(const T& x) noexcept { return x; }
	inline auto to_outputable(const char* str) { return utils::ansi_to_unicode(str); }	// 非ASCIIを含むchar*をwcoutに流すと読み込み違反が発生するのでwchar_t*に変換する

	// 引数をカンマ区切りで出力します。
	inline void dump_parameters(std::wostream& out) {}	// 再帰終了
	template<class Head, class... Tail>
	void dump_parameters(std::wostream& out, const Head &head, const Tail&... tail)
	{
		out << L", " << utils::to_outputable(head);
		utils::dump_parameters(out, tail...);
	}

	inline void dump_named_parameters(std::wostream& out) {}	// 再帰終了
	template<class HeadValue, class... Tail>
	void dump_named_parameters(std::wostream&out, const std::wstring_view& name, const HeadValue& headValue, const Tail&... tail)
	{
		out << L", " << name << L": " << utils::to_outputable(headValue);
		utils::dump_named_parameters(out, tail...);
	}

	// unique_ptrのdeleter用関数オブジェクト
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
