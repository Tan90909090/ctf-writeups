#define _CRT_SECURE_NO_WARNINGS
#include"../CommonLib/utils.hpp"
#include"../CommonLib/portable_executable.hpp"
#include"../CommonLib/preprocessor.hpp"
#include"../CommonLib/dll_injection.hpp"
#include<iostream>
#include<format>
#pragma comment(lib, "../x64/Debug/CommonLib.lib")

using namespace std::literals::string_literals;

wchar_t g_modulePath[MAX_PATH];

[[noreturn]]
void show_message_and_exit(const std::wstring& message)
{
	::MessageBoxW(nullptr, message.c_str(), L"起動に失敗しました。", MB_OK | MB_ICONERROR);
	std::exit(EXIT_FAILURE);
}

void hex_dump(std::wostream& os, LPCVOID data, size_t size)
{
	for (size_t i = 0; i < size; ++i)
	{
		os << L"0x" << std::format(L"{:02x}", ((unsigned char*)data)[i]) << L", ";
	}
}

std::mutex g_consoleMutex{};
#define CONSOLE_OPERATION(...) \
	do \
	{ \
		if (auto lock = utils::make_unique_lock(g_consoleMutex, std::try_to_lock)) { \
			__VA_ARGS__; \
		} \
	} while (0)

#define DEFINE_STORE_VARIABLE_AND_DECLARE_FUNCTION(api, ...) \
	decltype(api)* g_original##api; \
	auto WINAPI Hooked##api(__VA_ARGS__)	// ここから先は波括弧含めて実装側が作る
#define DEFINE_STORE_VARIABLE_AND_FORWARD_FUNCTION_NO_PARAM(api) \
	DEFINE_STORE_VARIABLE_AND_DECLARE_FUNCTION(api) \
	{ \
		CONSOLE_OPERATION(std::wcout << L#api); \
		auto result = g_original##api(); \
		CONSOLE_OPERATION(std::wcout << L", result:" << result << std::endl); \
		return result; \
	}
#define DEFINE_STORE_VARIABLE_AND_FORWARD_FUNCTION(api, ...) \
	DEFINE_STORE_VARIABLE_AND_DECLARE_FUNCTION(api, __VA_ARGS__) \
	{ \
		CONSOLE_OPERATION( \
			std::wcout << L#api, \
			utils::dump_parameters(std::wcout, __VA_ARGS__)); \
		auto result = g_original##api(__VA_ARGS__); \
		CONSOLE_OPERATION(std::wcout << L", result:" << result << std::endl); \
		return result; \
	}	// マクロ使用側で末尾セミコロンを省略できてしまうけれど妥協
#define HOOK_API(imagePE, filePE, api) \
	do \
	{ \
		g_original##api = utils::hook_api(imagePE, filePE, #api, Hooked##api); \
		CONSOLE_OPERATION(std::wcout << (g_original##api == nullptr ? L"Failed" : L"Succeeded") << L" to hook " << #api << std::endl); \
	} while(0)

// dump_named_parameters()に渡す引数リストを作成するマクロ
// http://stackoverflow.com/questions/824639/variadic-recursive-preprocessor-macros-is-it-possible
// VC++は可変長マクロにバグがある http://stackoverflow.com/questions/36925989/how-to-define-recursive-variadic-macros
#define NAMED_MEMBER_LIST_1(pStruct, m     ) L#m, (pStruct)->m
#define NAMED_MEMBER_LIST_2(pStruct, m, ...) L#m, (pStruct)->m, IDENTITY(NAMED_MEMBER_LIST_1(pStruct, __VA_ARGS__))
#define NAMED_MEMBER_LIST_3(pStruct, m, ...) L#m, (pStruct)->m, IDENTITY(NAMED_MEMBER_LIST_2(pStruct, __VA_ARGS__))
#define NAMED_MEMBER_LIST_4(pStruct, m, ...) L#m, (pStruct)->m, IDENTITY(NAMED_MEMBER_LIST_3(pStruct, __VA_ARGS__))
#define NAMED_MEMBER_LIST_5(pStruct, m, ...) L#m, (pStruct)->m, IDENTITY(NAMED_MEMBER_LIST_4(pStruct, __VA_ARGS__))
#define NAMED_MEMBER_LIST_6(pStruct, m, ...) L#m, (pStruct)->m, IDENTITY(NAMED_MEMBER_LIST_5(pStruct, __VA_ARGS__))
#define NAMED_MEMBER_LIST_7(pStruct, m, ...) L#m, (pStruct)->m, IDENTITY(NAMED_MEMBER_LIST_6(pStruct, __VA_ARGS__))
#define NAMED_MEMBER_LIST_8(pStruct, m, ...) L#m, (pStruct)->m, IDENTITY(NAMED_MEMBER_LIST_7(pStruct, __VA_ARGS__))
#define NAMED_MEMBER_LIST(pStruct, ...) IDENTITY(NUMBERED_IDENTIFIER(NAMED_MEMBER_LIST_, __VA_ARGS__)(pStruct, __VA_ARGS__))

#define NAMED_EXPRESSION_LIST_1(e     ) L#e, (e)
#define NAMED_EXPRESSION_LIST_2(e, ...) L#e, (e), IDENTITY(NAMED_EXPRESSION_LIST_1(__VA_ARGS__))
#define NAMED_EXPRESSION_LIST_3(e, ...) L#e, (e), IDENTITY(NAMED_EXPRESSION_LIST_2(__VA_ARGS__))
#define NAMED_EXPRESSION_LIST_4(e, ...) L#e, (e), IDENTITY(NAMED_EXPRESSION_LIST_3(__VA_ARGS__))
#define NAMED_EXPRESSION_LIST_5(e, ...) L#e, (e), IDENTITY(NAMED_EXPRESSION_LIST_4(__VA_ARGS__))
#define NAMED_EXPRESSION_LIST_6(e, ...) L#e, (e), IDENTITY(NAMED_EXPRESSION_LIST_5(__VA_ARGS__))
#define NAMED_EXPRESSION_LIST_7(e, ...) L#e, (e), IDENTITY(NAMED_EXPRESSION_LIST_6(__VA_ARGS__))
#define NAMED_EXPRESSION_LIST_8(e, ...) L#e, (e), IDENTITY(NAMED_EXPRESSION_LIST_7(__VA_ARGS__))
#define NAMED_EXPRESSION_LIST(...) IDENTITY(NUMBERED_IDENTIFIER(NAMED_EXPRESSION_LIST_, __VA_ARGS__)(__VA_ARGS__))

void* g_destBuffer;

DEFINE_STORE_VARIABLE_AND_DECLARE_FUNCTION(DeviceIoControl, HANDLE hDevice, DWORD dwIoControlCode, LPVOID lpInBuffer, DWORD nInBufferSize, LPVOID lpOutBuffer, DWORD nOutBufferSize, LPDWORD lpBytesReturned, LPOVERLAPPED lpOverlapped) {
	if (dwIoControlCode == 0x224014) {
		CONSOLE_OPERATION(std::wcout << L"DeviceIoControl before, dwIoControlCode: " << std::format(L"{:x}", dwIoControlCode) << L", current dest content: ",
			hex_dump(std::wcout, g_destBuffer, 64),
			std::wcout << std::endl);
	}

	auto result = g_originalDeviceIoControl(hDevice, dwIoControlCode, lpInBuffer, nInBufferSize, lpOutBuffer, nOutBufferSize, lpBytesReturned, lpOverlapped);
	CONSOLE_OPERATION({
		std::wcout << L"DeviceIoControl after, received: ";
		hex_dump(std::wcout, lpOutBuffer, nOutBufferSize);
		std::wcout << std::endl;
	});
	if (dwIoControlCode == 0x224010)
	{
		static int s_count = 0;
		static const char* arrayOffset[11][2] =
		{
			{"GUY", nullptr}, // memcpy(dest, src, 0x1000)用、入力文字列がそのまま入る
			// initial block(=IV?), AES-key どちらも16バイトのはず
			{"COW", "BAT"},
			{"EYE", "SPE"},
			{"ABC", "WIN"},
			{"ICE", "CRY"},
			{"DOG", "CAT"},
			{"ATK", "VIM"},
			{"RED", "ZIP"},
			{"QRS", "DEF"},
			{"MOO", "AIR"},
			{"EGG", nullptr}, // memcmp(buf1, buf2, 0x40)用、親プロセスで何か格納した値が入っている
		};
		if (1 <= s_count && s_count <= 9 || true)
		{
			DWORD_PTR base_addr = (*(DWORD_PTR*)(lpOutBuffer)) << 39;
			for (int i = 0; i < 2; ++i)
			{
				auto str = arrayOffset[s_count][i];
				if (str == nullptr) { continue; }

				wchar_t wstr[4] = { str[0], str[1], str[2], 0 };
				DWORD_PTR offset = str[0] | (str[1] << 8) | (str[2] << 16);
				auto addr = reinterpret_cast<LPCVOID>(base_addr + (offset << 12));
				
				// VMMapで見ても割り当てられていないメモリ領域を何かされている可能性がある？
				MEMORY_BASIC_INFORMATION mbi;
				if (::VirtualQuery(addr, &mbi, sizeof(mbi)) > 0)
				{
					if (mbi.Protect == PAGE_READONLY || mbi.Protect == PAGE_READWRITE || mbi.Protect == PAGE_EXECUTE_READ || mbi.Protect == PAGE_EXECUTE_READWRITE || true)
					{
						CONSOLE_OPERATION({
							std::wcout << L"DeviceIoControl(code: 0x224010) addr: " << std::format(L"{:016x}", addr) << " (" << wstr << L"): ";
							hex_dump(std::wcout, addr, 16);
							std::wcout << std::endl;
							});
					}
					else
					{
						CONSOLE_OPERATION({
							std::wcout << L"DeviceIoControl(code: 0x224010) addr: " << std::format(L"{:016x}", addr) << " (" << wstr << L"): can not read! (" << std::format(L"{:x}", mbi.Protect) << L")\n";
							});
					}
				}
				else
				{
					CONSOLE_OPERATION({
						std::wcout << L"DeviceIoControl(code: 0x224010) addr: " << std::format(L"{:016x}", addr) << " (" << wstr << L"): is not committed!\n";
						});
				}
			}
		}
		s_count++;
	}
	return result;
}
DEFINE_STORE_VARIABLE_AND_DECLARE_FUNCTION(WaitForDebugEvent, LPDEBUG_EVENT lpDebugEvent, DWORD dwMilliseconds) {
	//CONSOLE_OPERATION(std::wcout << L"WaitForDebugEvent before",
	//	utils::dump_named_parameters(std::wcout, NAMED_EXPRESSION_LIST(lpDebugEvent->dwDebugEventCode)),
	//	std::wcout << std::endl);
	auto result = g_originalWaitForDebugEvent(lpDebugEvent, dwMilliseconds);
	if (lpDebugEvent->dwDebugEventCode == EXCEPTION_DEBUG_EVENT)
	{
		CONSOLE_OPERATION(std::wcout << L"WaitForDebugEvent after",
			utils::dump_named_parameters(std::wcout, NAMED_EXPRESSION_LIST(lpDebugEvent->u.Exception.ExceptionRecord.ExceptionCode)),
			std::wcout << std::endl);
	}

	return result;
}
DEFINE_STORE_VARIABLE_AND_DECLARE_FUNCTION(ContinueDebugEvent, DWORD dwProcessId, DWORD dwThreadId, DWORD dwContinueStatus) {
	CONSOLE_OPERATION(std::wcout << L"ContinueDebugEvent before",
		utils::dump_named_parameters(std::wcout, NAMED_EXPRESSION_LIST(dwContinueStatus)),
		std::wcout << std::endl);
	return g_originalContinueDebugEvent(dwProcessId, dwThreadId, dwContinueStatus);
}
DEFINE_STORE_VARIABLE_AND_DECLARE_FUNCTION(GetThreadContext, HANDLE hThread, LPCONTEXT lpContext) {
	auto result = g_originalGetThreadContext(hThread, lpContext);
	CONSOLE_OPERATION(std::wcout << L"GetThreadContext after",
		utils::dump_named_parameters(std::wcout, NAMED_EXPRESSION_LIST(lpContext->Rax, lpContext->Rip)),
		std::wcout << std::endl);
	return result;
}
DEFINE_STORE_VARIABLE_AND_DECLARE_FUNCTION(SetThreadContext, HANDLE hThread, const CONTEXT* lpContext) {
	CONSOLE_OPERATION(std::wcout << L"SetThreadContext before",
		utils::dump_named_parameters(std::wcout, NAMED_EXPRESSION_LIST(lpContext->Rax, lpContext->Rip)),
		std::wcout << std::endl);
	return g_originalSetThreadContext(hThread, lpContext);
}
DEFINE_STORE_VARIABLE_AND_DECLARE_FUNCTION(CreateProcessA, LPCSTR                lpApplicationName,
	LPSTR                 lpCommandLine,
	LPSECURITY_ATTRIBUTES lpProcessAttributes,
	LPSECURITY_ATTRIBUTES lpThreadAttributes,
	BOOL                  bInheritHandles,
	DWORD                 dwCreationFlags,
	LPVOID                lpEnvironment,
	LPCSTR                lpCurrentDirectory,
	LPSTARTUPINFOA        lpStartupInfo,
	LPPROCESS_INFORMATION lpProcessInformation) {
	CONSOLE_OPERATION(std::wcout << L"CreateProcessA before\n");
	// 子プロセスにもこれを注入する。
	auto result = g_originalCreateProcessA(
		lpApplicationName,
		lpCommandLine,
		lpProcessAttributes,
		lpThreadAttributes,
		bInheritHandles,
		CREATE_SUSPENDED | CREATE_NEW_CONSOLE,	// dwCreationFlags | CREATE_SUSPENDED, // CREATE_SUSPENDEDとDEBUG_ONLY_THIS_PROCESSの両方の指定があると、CreateRemoteThreadしたものも全部Suspendedになって都合が悪い
		lpEnvironment,
		lpCurrentDirectory,
		lpStartupInfo,
		lpProcessInformation);
	CONSOLE_OPERATION(std::wcout << L"CreateProcessA after, result = " << result << std::endl);
	try {
		CONSOLE_OPERATION(std::wcout << L"CreateProcessA hook child process\n",
			utils::dump_named_parameters(std::wcout, NAMED_EXPRESSION_LIST(lpProcessInformation->dwProcessId)),
			std::wcout << std::endl);
		utils::inject_hook_dll(lpProcessInformation->hProcess, g_modulePath);
	}
	catch (const utils::wide_exception& ex)
	{
		show_message_and_exit(ex.wide_what());
	}
	catch (const std::exception& ex)
	{
		show_message_and_exit(L"処理に失敗しました: " + utils::ansi_to_unicode(ex.what()));
	}
	CONSOLE_OPERATION(std::wcout << L"CreateProcessA DebugActiveProcess\n");
	auto result1 = ::DebugActiveProcess(lpProcessInformation->dwProcessId);
	CONSOLE_OPERATION(std::wcout << L"CreateProcessA DebugActiveProcess, result = " << result1 << std::endl);
	CONSOLE_OPERATION(std::wcout << L"CreateProcessA ResumeThread\n");
	auto result2 = ::ResumeThread(lpProcessInformation->hThread);
	CONSOLE_OPERATION(std::wcout << L"CreateProcessA ResumeThread, result = " << result2 << std::endl);
	CONSOLE_OPERATION(std::wcout << L"CreateProcessA complete\n");
	return (BOOL)(result && result1 && result2);
}

decltype(memcpy)* g_originalmemcpy;
auto __cdecl Hookedmemcpy(LPVOID dest, LPCVOID src, size_t count) {
	g_destBuffer = dest;
	CONSOLE_OPERATION(
		std::wcout << L"memcpy, dest(" << std::format(L"{:16x}", dest) << L") = src(" << std::format(L"{:08x}", src) << L") : ",
		hex_dump(std::wcout, src, 0x100), // 入力文字列コピー箇所でだけ使っているけど、0x1000もコピーしている。代わりに固定値を使う
		std::wcout << std::endl);
	return g_originalmemcpy(dest, src, count);
}
decltype(memcmp)* g_originalmemcmp;
auto __cdecl Hookedmemcmp(LPCVOID buffer1, LPCVOID buffer2, size_t count) {
	CONSOLE_OPERATION(
		std::wcout << L"memcmp, \nbuffer1: ",
		hex_dump(std::wcout, buffer1, count),
		std::wcout << L"\nbuffer2: ",
		hex_dump(std::wcout, buffer2, count),
		std::wcout << std::endl);
	return g_originalmemcmp(buffer1, buffer2, count);
}
decltype(puts)* g_originalputs;
auto __cdecl Hookedputs(const char*buffer) {
	auto result = g_originalputs(buffer);
	fflush(stdout);
	CONSOLE_OPERATION(std::wcout << L"puts! Wait!\n");
	Sleep(INFINITE);
	return result;
}

DEFINE_STORE_VARIABLE_AND_DECLARE_FUNCTION(TerminateProcess, HANDLE hProcess, UINT uExitCode)
{
	CONSOLE_OPERATION(std::wcout << L"TerminateProcess! Wait!\n");
	Sleep(INFINITE);
	return g_originalTerminateProcess(hProcess, uExitCode);
}
DEFINE_STORE_VARIABLE_AND_DECLARE_FUNCTION(ExitProcess, UINT uExitCode)
{
	CONSOLE_OPERATION(std::wcout << L"ExitProcess! Wait!\n");
	Sleep(INFINITE);
	return g_originalExitProcess(uExitCode);
}

void hook_apis()
{
#if 1
	::AllocConsole();
	// local設定なしだとwchar_t*で非ASCIIが出せない local設定するとchar*で非ASCIIが出せない
	std::locale::global(std::locale(""));
	// http://stackoverflow.com/questions/5257509/freopen-equivalent-for-c-streams freopenでiostreamのも変更される imbueしなくてもwcoutで正常に表示された
	std::ignore = std::freopen("CONIN$", "r", stdin);
	std::ignore = std::freopen("CONOUT$", "w", stdout);
#endif

	CONSOLE_OPERATION(std::wcout << L"exeImage\n");
	utils::portable_executable exeImage{ ::GetModuleHandleA(nullptr) };
	CONSOLE_OPERATION(std::wcout << L"exeFile\n");
	utils::portable_executable exeFile{ utils::get_current_exe_path() };

	HOOK_API(exeImage, exeFile, DeviceIoControl);
	//HOOK_API(exeImage, exeFile, WaitForDebugEvent);
	//HOOK_API(exeImage, exeFile, ContinueDebugEvent);
	HOOK_API(exeImage, exeFile, GetThreadContext);
	HOOK_API(exeImage, exeFile, SetThreadContext);
	HOOK_API(exeImage, exeFile, CreateProcessA);
	HOOK_API(exeImage, exeFile, memcpy);
	HOOK_API(exeImage, exeFile, memcmp);
	HOOK_API(exeImage, exeFile, puts);
	HOOK_API(exeImage, exeFile, TerminateProcess);
	HOOK_API(exeImage, exeFile, ExitProcess);
}

[[noreturn]]
void show_failed_to_hook_message_and_exit(const std::wstring & str)
{
	::MessageBoxW(nullptr, str.c_str(), L"APIフックに失敗しました。", MB_OK | MB_ICONERROR);
	std::exit(1);	// 注入側はスレッドの終了コードが0ならエラーと判断しているので、それ以外で終わらせる
}

BOOL APIENTRY DllMain(HMODULE hinstDLL, DWORD  fdwReason, LPVOID lpReserved)
{
	switch (fdwReason)
	{
	case DLL_PROCESS_ATTACH:
		::DisableThreadLibraryCalls(hinstDLL);
		try
		{
			::GetModuleFileNameW(hinstDLL, g_modulePath, sizeof(g_modulePath) / sizeof(g_modulePath[0]));
			CONSOLE_OPERATION(std::wcout << L"after GetModuleFileNameW, result: " << g_modulePath << std::endl);
			::hook_apis();
		}
		catch (const utils::wide_exception& ex)
		{
			show_failed_to_hook_message_and_exit(L"APIフックに失敗しました。"s + ex.wide_what());
		}
		catch (const std::exception& ex)
		{
			show_failed_to_hook_message_and_exit(L"APIフックに失敗しました: " + utils::ansi_to_unicode(ex.what()));
		}
		break;
	}

	return TRUE;
}
