#pragma once

// http://stackoverflow.com/questions/5530505/why-does-this-variadic-argument-count-macro-fail-with-vc
#define IDENTITY(x) x
// �����̌����擾���܂��B
#define PP_NARGS(...)  IDENTITY(PP_NARGS_IMPL(__VA_ARGS__,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0))
#define PP_NARGS_IMPL(x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,N,...) N

// ���ʎq�ƈ����̌���\�����l�Ƃ��������܂��B
#define NUMBERED_IDENTIFIER(identifier, ...) NUMBERED_IDENTIFIER_(identifier, PP_NARGS(__VA_ARGS__))
#define NUMBERED_IDENTIFIER_(identifier, num) NUMBERED_IDENTIFIER__(identifier, num)
#define NUMBERED_IDENTIFIER__(identifier, num) identifier##num
