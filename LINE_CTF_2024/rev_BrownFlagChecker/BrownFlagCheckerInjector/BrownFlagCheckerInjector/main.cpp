#include"../CommonLib/utils.hpp"
#include"../CommonLib/dll_injection.hpp"
#include<locale>
#include<cassert>
#include<iostream>
#pragma comment(lib, "../x64/Debug/CommonLib.lib")

[[noreturn]]
void show_message_and_exit(const std::wstring& message)
{
	::MessageBoxW(nullptr, message.c_str(), L"起動に失敗しました。", MB_OK | MB_ICONERROR);
	std::exit(EXIT_FAILURE);
}

[[noreturn]]
void show_file_not_found_message(const fs::path& filepath)
{
	show_message_and_exit(L"ファイル " + filepath.native() + L" が見つかりませんでした。");
}

int main()
{
	try
	{
		std::wcout << L"this is main.cpp\n";
		std::locale::global(std::locale(""));

		constexpr auto injectDllName = L"BrownFlagCheckerHook.dll";
		constexpr auto targetExeName = L"BrownFlagChecker.exe";
		constexpr auto commandLineParameter = L"";

		const auto currentExePath = utils::get_current_exe_path();
		if (!fs::is_regular_file(currentExePath)) { show_message_and_exit(L"Injector.exeのパスの取得に失敗しました。"); }

		const auto currentDirectoryPath = currentExePath.parent_path();
		const auto injectDllPath = currentDirectoryPath / injectDllName;
		if (!fs::is_regular_file(injectDllPath)) { show_file_not_found_message(injectDllPath); }

		const auto targetExePath = currentDirectoryPath / targetExeName;

		if (!fs::is_regular_file(targetExePath)) { show_file_not_found_message(targetExePath); }

		utils::create_process_and_inject_and_wait(targetExePath, commandLineParameter, injectDllPath);

		return EXIT_SUCCESS;
	}
	catch (const utils::wide_exception& ex)
	{
		show_message_and_exit(ex.wide_what());
	}
	catch (const std::exception& ex)
	{
		show_message_and_exit(L"処理に失敗しました: " + utils::ansi_to_unicode(ex.what()));
	}
}
