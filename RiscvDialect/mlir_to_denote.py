import re
import sys

def convert_llvm_func_to_denote(llvm_code: str) -> str:
    # Extract the function name
    name_match = re.search(r"@(\w+)\(", llvm_code)
    func_name = name_match.group(1) if name_match else "unknown"

    # Extract arguments
    args_match = re.search(r"@.+?\((.*?)\)", llvm_code, re.DOTALL)
    args_str = args_match.group(1).strip() if args_match else ""
    
    # Clean argument list: remove `{llvm.noundef}` and format args
    args = []
    for i, arg in enumerate(re.split(r",\s*", args_str)):
        if ':' in arg:
            arg_type = arg.split(':')[-1].strip().split()[0]
            args.append(f"%arg{i}: {arg_type}")
    args_formatted = ", ".join(args)

    # Extract body
    body_match = re.search(r"\{\s*(%.*?llvm\.return.*?)\s*\}", llvm_code, re.DOTALL)
    body = body_match.group(1).strip() if body_match else ""

    # Indent the body lines
    body_lines = ["  " + line.strip() for line in body.splitlines()]
    body_block = "\n".join(body_lines)

    # Construct final output
    output = f"""def {func_name} :=
  [llvm(64)| {{
    ^bb0({args_formatted}) :
{body_block}
  }}]"""

    return output


# Example usage
llvm_mlir_input2 = """
llvm.func local_unnamed_addr @sub_64(%arg0: i64 {llvm.noundef}, %arg1: i64 {llvm.noundef},%arg2: i64 {llvm.noundef}) -> i64 attributes {frame_pointer = #llvm.framePointerKind<"non-leaf">, memory = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", "ssp", ["uwtable", "1"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "apple-m1"]], target_cpu = "apple-m1", target_features = #llvm.target_features<["+aes", "+altnzcv", "+ccdp", "+ccidx", "+complxnum", "+crc", "+dit", "+dotprod", "+flagm", "+fp-armv8", "+fp16fml", "+fptoint", "+fullfp16", "+jsconv", "+lse", "+neon", "+pauth", "+perfmon", "+predres", "+ras", "+rcpc", "+rdm", "+sb", "+sha2", "+sha3", "+specrestrict", "+ssbs", "+v8.1a", "+v8.2a", "+v8.3a", "+v8.4a", "+v8a", "+zcm", "+zcz"]>, will_return} {
    %0 = llvm.sub %arg1, %arg0 overflow<nsw> : i64
    llvm.return %0 : i64
  }
    """

print(convert_llvm_func_to_denote(llvm_mlir_input2))
def main():
    if len(sys.argv) != 2:
        print("Usage: parserMLIR.py <input.mlir>")
        sys.exit(1)

    input_path = sys.argv[1]

    try:
        with open(input_path, 'r', encoding='utf-8') as f:
            content = f.read()

        result = convert_llvm_func_to_denote(content)
        print(result)

    except FileNotFoundError:
        print(f"Error: File '{input_path}' not found.")
        sys.exit(1)
if __name__ == "__main__":
    main()