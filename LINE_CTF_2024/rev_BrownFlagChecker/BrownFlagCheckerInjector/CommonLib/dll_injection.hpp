#pragma once

#include"utils.hpp"

namespace utils {
	// �w��v���Z�X��DLL�C���W�F�N�V�������s���܂��B
	void inject_hook_dll(HANDLE hProcess, const fs::path& dllPath);

	// �w��EXE��SUSPENDED��ԂŋN�����ADLL�C���W�F�N�V�������s���܂��BDLL�C���W�F�N�V����������Ƀv���Z�X�̎��s���ĊJ���܂��B
	void create_process_and_inject_and_wait(
		const fs::path& exePath,
		const std::wstring& commandLineParameter,
		const fs::path& injectDllPath);
}
