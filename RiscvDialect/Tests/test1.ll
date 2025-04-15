; ModuleID = 'simpleInstructionLoweringTest.c'
source_filename = "simpleInstructionLoweringTest.c"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128-Fn32"
target triple = "arm64-apple-macosx13.0.0"

;unoptimized version, then run llvm super optimizer 

; Function Attrs: noinline nounwind ssp uwtable(sync)
define i64 @add_64(i64 noundef %0, i64 noundef %1) #0 {
  %3 = alloca i64, align 8
  %4 = alloca i64, align 8
  store i64 %0, ptr %3, align 8
  store i64 %1, ptr %4, align 8
  %5 = load i64, ptr %3, align 8
  %6 = load i64, ptr %4, align 8
  %7 = add nsw i64 %5, %6
  ret i64 %7
}

; Function Attrs: noinline nounwind ssp uwtable(sync)
define i64 @sub_64(i64 noundef %0, i64 noundef %1) #0 {
  %3 = alloca i64, align 8
  %4 = alloca i64, align 8
  store i64 %0, ptr %3, align 8
  store i64 %1, ptr %4, align 8
  %5 = load i64, ptr %3, align 8
  %6 = load i64, ptr %4, align 8
  %7 = sub nsw i64 %5, %6
  ret i64 %7
}

; Function Attrs: noinline nounwind ssp uwtable(sync)
define i64 @mul_64(i64 noundef %0, i64 noundef %1) #0 {
  %3 = alloca i64, align 8
  %4 = alloca i64, align 8
  store i64 %0, ptr %3, align 8
  store i64 %1, ptr %4, align 8
  %5 = load i64, ptr %3, align 8
  %6 = load i64, ptr %4, align 8
  %7 = mul nsw i64 %5, %6
  ret i64 %7
}

; Function Attrs: noinline nounwind ssp uwtable(sync)
define i64 @div_64(i64 noundef %0, i64 noundef %1) #0 {
  %3 = alloca i64, align 8
  %4 = alloca i64, align 8
  store i64 %0, ptr %3, align 8
  store i64 %1, ptr %4, align 8
  %5 = load i64, ptr %3, align 8
  %6 = load i64, ptr %4, align 8
  %7 = sdiv i64 %5, %6
  ret i64 %7
}

; Function Attrs: noinline nounwind ssp uwtable(sync)
define i64 @rem_64(i64 noundef %0, i64 noundef %1) #0 {
  %3 = alloca i64, align 8
  %4 = alloca i64, align 8
  store i64 %0, ptr %3, align 8
  store i64 %1, ptr %4, align 8
  %5 = load i64, ptr %3, align 8
  %6 = load i64, ptr %4, align 8
  %7 = srem i64 %5, %6
  ret i64 %7
}

; Function Attrs: noinline nounwind ssp uwtable(sync)
define i32 @main() #0 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  %8 = call i32 @rand()
  store i32 %8, ptr %1, align 4
  %9 = call i32 @rand()
  store i32 %9, ptr %2, align 4
  %10 = load i32, ptr %1, align 4
  %11 = sext i32 %10 to i64
  %12 = load i32, ptr %2, align 4
  %13 = sext i32 %12 to i64
  %14 = call i64 @add_64(i64 noundef %11, i64 noundef %13)
  %15 = trunc i64 %14 to i32
  store i32 %15, ptr %3, align 4
  %16 = load i32, ptr %1, align 4
  %17 = sext i32 %16 to i64
  %18 = load i32, ptr %2, align 4
  %19 = sext i32 %18 to i64
  %20 = call i64 @sub_64(i64 noundef %17, i64 noundef %19)
  %21 = trunc i64 %20 to i32
  store i32 %21, ptr %4, align 4
  %22 = load i32, ptr %1, align 4
  %23 = sext i32 %22 to i64
  %24 = load i32, ptr %2, align 4
  %25 = sext i32 %24 to i64
  %26 = call i64 @mul_64(i64 noundef %23, i64 noundef %25)
  %27 = trunc i64 %26 to i32
  store i32 %27, ptr %5, align 4
  %28 = load i32, ptr %1, align 4
  %29 = sext i32 %28 to i64
  %30 = load i32, ptr %2, align 4
  %31 = sext i32 %30 to i64
  %32 = call i64 @div_64(i64 noundef %29, i64 noundef %31)
  %33 = trunc i64 %32 to i32
  store i32 %33, ptr %6, align 4
  %34 = load i32, ptr %1, align 4
  %35 = sext i32 %34 to i64
  %36 = load i32, ptr %2, align 4
  %37 = sext i32 %36 to i64
  %38 = call i64 @rem_64(i64 noundef %35, i64 noundef %37)
  %39 = trunc i64 %38 to i32
  store i32 %39, ptr %7, align 4
  ret i32 0
}

declare i32 @rand() #1

attributes #0 = { noinline nounwind ssp uwtable(sync) "frame-pointer"="non-leaf" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="apple-m1" "target-features"="+aes,+altnzcv,+ccdp,+ccidx,+complxnum,+crc,+dit,+dotprod,+flagm,+fp-armv8,+fp16fml,+fptoint,+fullfp16,+jsconv,+lse,+neon,+pauth,+perfmon,+predres,+ras,+rcpc,+rdm,+sb,+sha2,+sha3,+specrestrict,+ssbs,+v8.1a,+v8.2a,+v8.3a,+v8.4a,+v8a,+zcm,+zcz" }
attributes #1 = { "frame-pointer"="non-leaf" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="apple-m1" "target-features"="+aes,+altnzcv,+ccdp,+ccidx,+complxnum,+crc,+dit,+dotprod,+flagm,+fp-armv8,+fp16fml,+fptoint,+fullfp16,+jsconv,+lse,+neon,+pauth,+perfmon,+predres,+ras,+rcpc,+rdm,+sb,+sha2,+sha3,+specrestrict,+ssbs,+v8.1a,+v8.2a,+v8.3a,+v8.4a,+v8a,+zcm,+zcz" }

!llvm.module.flags = !{!0, !1, !2, !3, !4}
!llvm.ident = !{!5}

!0 = !{i32 2, !"SDK Version", [2 x i32] [i32 13, i32 3]}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{i32 8, !"PIC Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 1}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Homebrew clang version 19.1.7"}
