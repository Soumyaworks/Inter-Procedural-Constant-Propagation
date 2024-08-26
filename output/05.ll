; ModuleID = '/home/aayusphere/IPACO/llvm-project/InterProcCP/05.ll'
source_filename = "/home/aayusphere/IPACO/llvm-project/InterProcCP/05.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@.str = private unnamed_addr constant [3 x i8] c"%d\00", align 1

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 {
entry:
  %l = alloca i32, align 4
  store i32 40, i32* %l, align 4
  call void @fun(i32 noundef 10, i32 noundef 100, i32 noundef 1000)
  call void @bar(i32 noundef 1000, i32 noundef 400, i32 noundef 300)
  call void @foo(i32 noundef 100, i32 noundef 400, i32 noundef 1000, i32 noundef 40)
  ret i32 0
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @fun(i32 noundef %i, i32 noundef %j, i32 noundef %k) #0 {
entry:
  %i.addr = alloca i32, align 4
  %j.addr = alloca i32, align 4
  %k.addr = alloca i32, align 4
  %o = alloca i32, align 4
  %q = alloca i32, align 4
  %a = alloca i32, align 4
  store i32 %i, i32* %i.addr, align 4
  store i32 %j, i32* %j.addr, align 4
  store i32 %k, i32* %k.addr, align 4
  call void @bar(i32 noundef 2000, i32 noundef 10, i32 noundef 1000)
  store i32 20, i32* %o, align 4
  store i32 2, i32* %q, align 4
  store i32 400, i32* %a, align 4
  call void @foo(i32 noundef 100, i32 noundef 400, i32 noundef 1000, i32 noundef 800)
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @bar(i32 noundef %i, i32 noundef %j, i32 noundef %k) #0 {
entry:
  %i.addr = alloca i32, align 4
  %j.addr = alloca i32, align 4
  %k.addr = alloca i32, align 4
  store i32 %i, i32* %i.addr, align 4
  store i32 %j, i32* %j.addr, align 4
  store i32 %k, i32* %k.addr, align 4
  %0 = load i32, i32* %k.addr, align 4
  %1 = load i32, i32* %i.addr, align 4
  %mul = mul nsw i32 %0, %1
  %div = sdiv i32 %mul, 2
  store i32 %div, i32* %j.addr, align 4
  %2 = load i32, i32* %j.addr, align 4
  %call = call i32 (i8*, ...) @printf(i8* noundef getelementptr inbounds ([3 x i8], [3 x i8]* @.str, i64 0, i64 0), i32 noundef %2)
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @foo(i32 noundef %i, i32 noundef %j, i32 noundef %k, i32 noundef %x) #0 {
entry:
  %i.addr = alloca i32, align 4
  %j.addr = alloca i32, align 4
  %k.addr = alloca i32, align 4
  %x.addr = alloca i32, align 4
  store i32 %i, i32* %i.addr, align 4
  store i32 %j, i32* %j.addr, align 4
  store i32 %k, i32* %k.addr, align 4
  store i32 %x, i32* %x.addr, align 4
  store i32 1500, i32* %x.addr, align 4
  %call = call i32 (i8*, ...) @printf(i8* noundef getelementptr inbounds ([3 x i8], [3 x i8]* @.str, i64 0, i64 0), i32 noundef 1500)
  ret void
}

declare dso_local i32 @printf(i8* noundef, ...) #1

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"uwtable", i32 1}
!2 = !{i32 7, !"frame-pointer", i32 2}
!3 = !{!"clang version 14.0.6 (https://github.com/llvm/llvm-project.git f28c006a5895fc0e329fe15fead81e37457cb1d1)"}
