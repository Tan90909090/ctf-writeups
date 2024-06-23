#!/usr/bin/env python3

import re

HEADER = """

z3_codes = `#!/usr/bin/env python3

import z3
BIT = 16
flag = [z3.BitVec(f"flag{i:02}", BIT) for i in range(32)]
exp =[z3.BitVec(f"exp{i:02}", BIT) for i in range(12098)]
solver = z3.Solver()

for f in flag:
    solver.add(f >= 0x20)
    solver.add(f <= 0x7E)
`;

class Symbol
{
    constructor(expr)
    {
        this.expr = expr;
    }
    toString()
    {
        return this.expr;
    }
}

then_count = 0;
class SymbolThenable
{
    constructor(executer)
    {
        this.promise = new Promise(executer);
        this.v = undefined;
    }

    then(onFulfilled, onRejected)
    {
        return this.promise.then(v =>
            {
                this.v = v;
                const exp = `exp[${then_count}]`;
                if (then_count > 0) // 最初は「await new Promise((VXzWAkPODJDoQpyz => {略}));」で、それには引数がないのでundefinedになる。ソルバーには不要。
                {
                    z3_codes += `solver.add(${exp} == ${v})\\n`;
                }
                then_count++;
                return onFulfilled(exp);
            },
            onRejected)
    }
}

const symbol_add = (lhv, rhv) =>
    {
        if ((lhv instanceof Symbol) || (rhv instanceof Symbol))
            return new Symbol(`(${lhv.toString()}) + (${rhv.toString()})`);
        return lhv + rhv;
    };
const symbol_mul = (lhv, rhv) =>
    {
        if ((lhv instanceof Symbol) || (rhv instanceof Symbol))
            return new Symbol(`(${lhv.toString()}) * (${rhv.toString()})`);
        return lhv * rhv;
    };

const symbol_shr = (lhv, rhv) =>
    {
        return new Symbol(`z3.LShR(${lhv.toString()}, ${rhv.toString()})`);
    };

const symbol_band = (lhv, rhv) =>
    {
        return new Symbol(`(${lhv.toString()}) & (${rhv.toString()})`);
    };

const symbol_not = (lhv) =>
    {
        return new Symbol(`z3.If((${lhv.toString()}) == 0, z3.BitVecVal(1, BIT), z3.BitVecVal(0, BIT))`);
    };

const symbol_lt_condition = (lt_lhv, lt_rhv, condition_true, condition_false) =>
    {
        return new Symbol(`z3.If((${lt_lhv.toString()}) < (${lt_rhv.toString()}), ${condition_true.toString()}, ${condition_false.toString()})`);
    };

prompt_count = 0
original_prompt = prompt
prompt = (x) =>
    {
        const symbol = new Symbol(`flag[${prompt_count}]`);
        prompt_count++;
        return symbol;
    };

original_BigInt = BigInt
BigInt = (x) =>
    {
        console.log(x);
        return original_BigInt(x);
    };

original_alert = alert
alert = (msg) =>
    {
        z3_codes += `
solver.add(exp[${then_count - 1}] != 0)

if solver.check() != z3.sat:
    raise Exception("Can not solve...")
model = solver.model()
for f in flag:
    print(chr(model[f].as_long()), end="")
print()
`;
        console.log(z3_codes);
        original_alert(msg);
    };
"""

with open("promise_deobfuscated.js") as f:
    js = f.read()
with open("promise_converted.js", "w") as f:
    f.write(HEADER)
    for line in js.split("\n"):
        # この後一単語で処理させるために強引にまとめます
        line = re.sub(r"await (\w+)", r"await\1", line)

        # 「(async () => yeFrLpumXRwKksSh(lbarHjWBfcaCFsrw++ * 173n + BigInt((prompt() || "").charCodeAt() || 0)))();」など
        line = re.sub(
            r"lbarHjWBfcaCFsrw\+\+ \* 173n \+ BigInt\(\(prompt\(\) \|\| \"\"\)\.charCodeAt\(\) \|\| 0\)",
            r"symbol_add(symbol_mul(lbarHjWBfcaCFsrw++, 173n), prompt())",
            line,
        )

        line = re.sub(r"(\w+) \+ (\w+)", r"symbol_add(\1, \2)", line)
        line = re.sub(r"(\w+) >> (\w+)", r"symbol_shr(\1, \2)", line)

        # await fHnHcsMHcBCdPgQh & BigInt(!await XLeTMfYwUPxeGcOL)
        line = re.sub(
            r"(\w+) & BigInt\(!(\w+)\)",
            r"symbol_band(\1, symbol_not(\2))",
            line,
        )
        # await xlUjhYPRekqNgpMX & BigInt(await hStTPJpnSdjteILQ)
        line = re.sub(r"(\w+) & BigInt\((\w+)\)", r"symbol_band(\1, \2)", line)

        line = re.sub(r"(\w+) & (1n)", r"symbol_band(\1, \2)", line)
        line = re.sub(
            r"(\w+) < (\w+) \? (\w+) : (\w+)",
            r"symbol_lt_condition(\1, \2, \3, \4)",
            line,
        )

        # awaitを元に戻します
        line = re.sub(r"await(\w+)", r"await \1", line)

        line = re.sub(r"new Promise", r"new SymbolThenable", line)

        f.write(line)
        f.write("\n")
