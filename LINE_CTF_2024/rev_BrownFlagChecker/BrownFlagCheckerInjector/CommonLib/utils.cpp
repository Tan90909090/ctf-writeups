#include"utils.hpp"
#include<array>
#include<iostream>

namespace utils
{
	std::wstring ansi_to_unicode(const char* ansiStr)
	{
		// http://stackoverflow.com/questions/27220/how-to-convert-stdstring-to-lpcwstr-in-c-unicode
		auto ansiLength = std::strlen(ansiStr) + 1;
		auto unicodeLength = ::MultiByteToWideChar(CP_ACP, 0, ansiStr, static_cast<int>(ansiLength), nullptr, 0);
		auto unicodeBuffer = std::make_unique<WCHAR[]>(unicodeLength);
		::MultiByteToWideChar(CP_ACP, 0, ansiStr, static_cast<int>(ansiLength), unicodeBuffer.get(), unicodeLength);
		return std::wstring{ unicodeBuffer.get() };
	}

	std::wstring get_last_error_message_as_unicode()
	{
		// http://stackoverflow.com/questions/1387064/how-to-get-the-error-message-from-the-error-code-returned-by-getlasterror
		auto messageId = ::GetLastError();
		std::array<WCHAR, 1024> buffer{};
		auto size = ::FormatMessageW(
			FORMAT_MESSAGE_FROM_SYSTEM | FORMAT_MESSAGE_IGNORE_INSERTS,
			nullptr,
			messageId,
			LANG_USER_DEFAULT,
			buffer.data(),
			static_cast<DWORD>(buffer.size()),
			nullptr);
		if (size == 0) { return std::wstring{ L"(�G���[���e�̎擾�Ɏ��s���܂���)" }; }

		std::wstring message{ buffer.data(), size };
		// �����̉��s�������폜
		auto pos = message.find_last_not_of(L"\r\n");
		if (pos != decltype(message)::npos)
		{
			message.erase(pos + 1);
		}
		return message;
	}

	fs::path get_current_exe_path()
	{
		std::array<wchar_t, MAX_PATH> buffer;
		auto size = ::GetModuleFileNameW(nullptr, buffer.data(), static_cast<DWORD>(buffer.size()));
		if ((size == 0) || (size == buffer.size() && ::GetLastError() == ERROR_INSUFFICIENT_BUFFER))
		{
			throw utils::wide_exception(L"EXE������p�X�̎擾�Ɏ��s���܂���: " + utils::get_last_error_message_as_unicode());
		}
		return fs::path{ buffer.data() };
	}
}
