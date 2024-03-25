#pragma once

#include"utils.hpp"

namespace utils {
	// 指定プロセスにDLLインジェクションを行います。
	void inject_hook_dll(HANDLE hProcess, const fs::path& dllPath);

	// 指定EXEをSUSPENDED状態で起動し、DLLインジェクションを行います。DLLインジェクション完了後にプロセスの実行を再開します。
	void create_process_and_inject_and_wait(
		const fs::path& exePath,
		const std::wstring& commandLineParameter,
		const fs::path& injectDllPath);
}
