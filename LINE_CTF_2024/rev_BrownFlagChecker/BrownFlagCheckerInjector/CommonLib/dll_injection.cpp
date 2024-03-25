#include"dll_injection.hpp"
#include<iostream>

namespace utils {
	namespace {
		auto create_suspended_process(const fs::path& exePath, const std::wstring& commandLineParameter)
		{
			std::wstring commandLineBuffer{ L'"' + exePath.native() + L'"' + L' ' + commandLineParameter };
			STARTUPINFO startupInfo{};
			startupInfo.cb = sizeof(startupInfo);

			std::unique_ptr<PROCESS_INFORMATION, utils::process_information_deleter> pProcessInfo{ new PROCESS_INFORMATION{} };
			if (!::CreateProcessW(
				exePath.c_str(),
				&commandLineBuffer[0],
				nullptr,
				nullptr,
				false,
				CREATE_SUSPENDED,
				nullptr,
				exePath.parent_path().c_str(),
				&startupInfo,
				pProcessInfo.get()))
			{
				throw utils::wide_exception(exePath.native() + L" �̋N���Ɏ��s���܂���: " + utils::get_last_error_message_as_unicode());
			}
			return pProcessInfo;
		}
	}

	void inject_hook_dll(HANDLE hProcess, const fs::path& dllPath)
	{
		auto virtualFreeExDeleter = [hProcess](LPVOID pAddress)
		{
			if (pAddress != nullptr)
			{
				::VirtualFreeEx(hProcess, pAddress, 0, MEM_RELEASE);
			}
		};

		std::wcout << "(DEBUG) VirtualAllocEx\n";
		auto writeSize = (dllPath.native().size() + 1) * sizeof(fs::path::value_type);
		std::unique_ptr<void, decltype(virtualFreeExDeleter)> pDllNameBuffer{
			::VirtualAllocEx(
				hProcess,
				nullptr,
				writeSize,
				MEM_COMMIT | MEM_RESERVE,
				PAGE_READWRITE),
			virtualFreeExDeleter };
		if (pDllNameBuffer.get() == nullptr)
		{
			throw utils::wide_exception(L"DLL�C���W�F�N�V�����p�̃������m�ۂɎ��s���܂���: " + utils::get_last_error_message_as_unicode());
		}

		std::wcout << "(DEBUG) WriteProcessMemory\n";
		SIZE_T writeBytes;
		if (!::WriteProcessMemory(
			hProcess,
			pDllNameBuffer.get(),
			dllPath.c_str(),
			writeSize,
			&writeBytes))
		{
			throw utils::wide_exception(L"DLL�C���W�F�N�V�����p�̃������������݂Ɏ��s���܂���: " + utils::get_last_error_message_as_unicode());
		}

		std::wcout << "(DEBUG) GetModuleHandleW\n";
		DWORD threadId = 0;
		auto hModule = ::GetModuleHandleW(L"kernel32.dll");
		if (hModule == nullptr)
		{
			throw utils::wide_exception(L"GetModuleHandleW�Ɏ��s���܂���: " + utils::get_last_error_message_as_unicode());
		}
		std::wcout << "(DEBUG) GetProcAddress\n";
		auto pLoadLibraryW = ::GetProcAddress(hModule, "LoadLibraryW");
		if (pLoadLibraryW == nullptr)
		{
			throw utils::wide_exception(L"GetProcAddress�Ɏ��s���܂���: " + utils::get_last_error_message_as_unicode());
		}
		std::wcout << "(DEBUG) pLoadLibraryW : " << pLoadLibraryW << L"\n";
		std::wcout << "(DEBUG) CreateRemoteThread\n";
		std::unique_ptr<HANDLE, utils::close_handle_deleter> hRemoteThread{
			::CreateRemoteThread(
				hProcess,
				nullptr,
				0,
				reinterpret_cast<LPTHREAD_START_ROUTINE>(pLoadLibraryW),
				pDllNameBuffer.get(),
				0,
				&threadId) };
		if (hRemoteThread.get() == nullptr)
		{
			throw utils::wide_exception(L"DLL�C���W�F�N�V�����p�̃X���b�h�쐬�Ɏ��s���܂���: " + utils::get_last_error_message_as_unicode());
		}

		std::wcout << "(DEBUG) threadId : " << threadId << L"\n";
		std::wcout << "(DEBUG) WaitForSingleObject\n";
		// �I������܂őҋ@
		::WaitForSingleObject(hRemoteThread.get(), INFINITE);
		DWORD exitCode;
		std::wcout << "(DEBUG) GetExitCodeThread\n";
		::GetExitCodeThread(hRemoteThread.get(), &exitCode);
		// ����̏ꍇ�A"The return value from the thread function."���I���R�[�h�Ƃ��Ď���̂ŁAnullptr(=0)�Ȃ玸�s���Ă���
		if (exitCode == 0)
		{
			throw utils::wide_exception(L"DLL�C���W�F�N�V�����p�̃X���b�h�������Ɏ��s���܂����B");
		}
	}

	void create_process_and_inject_and_wait(
		const fs::path& exePath,
		const std::wstring& commandLineParameter,
		const fs::path& injectDllPath)
	{
		// http://hp.vector.co.jp/authors/VA050396/tech_08.html
		auto pProcessInfo{ utils::create_suspended_process(exePath, commandLineParameter) };
		try
		{
			utils::inject_hook_dll(pProcessInfo->hProcess, injectDllPath);
			::ResumeThread(pProcessInfo->hThread);
			::WaitForSingleObject(pProcessInfo->hProcess, INFINITE);
		}
		catch (...)
		{
			::TerminateProcess(pProcessInfo->hProcess, EXIT_FAILURE);
			throw;
		}
	}
}
