
%"core::result::Result<core::ptr::non_null::NonNull<[u8]>, core::alloc::AllocError>::Err" = type { %"core::alloc::AllocError" }
%"core::alloc::AllocError" = type {}
%"core::result::Result<alloc::boxed::Box<core::mem::maybe_uninit::MaybeUninit<Nat>>, core::alloc::AllocError>::Err" = type { %"core::alloc::AllocError" }
%"alloc::alloc::Global" = type {}
%"core::mem::maybe_uninit::MaybeUninit<alloc::alloc::Global>" = type { [0 x i8] }
%"Vector<Nat>" = type { [2 x i64], {}* }
%"Vector<Nat>::Cons" = type { i64*, i64*, %"Vector<Nat>"* }
%"core::ptr::metadata::PtrRepr<[u8]>" = type { [2 x i64] }
%"core::result::Result<core::ptr::non_null::NonNull<u8>, core::alloc::AllocError>::Err" = type { %"core::alloc::AllocError" }
%"core::result::Result<core::convert::Infallible, core::alloc::AllocError>::Err" = type { %"core::alloc::AllocError" }
%"core::ops::control_flow::ControlFlow<core::result::Result<core::convert::Infallible, core::alloc::AllocError>, core::ptr::non_null::NonNull<[u8]>>::Break" = type { %"core::result::Result<core::convert::Infallible, core::alloc::AllocError>::Err" }
%"core::ops::control_flow::ControlFlow<core::result::Result<core::convert::Infallible, core::alloc::AllocError>, core::ptr::non_null::NonNull<u8>>::Break" = type { %"core::result::Result<core::convert::Infallible, core::alloc::AllocError>::Err" }
%"unwind::libunwind::_Unwind_Exception" = type { i64, void (i32, %"unwind::libunwind::_Unwind_Exception"*)*, [6 x i64] }
%"unwind::libunwind::_Unwind_Context" = type { [0 x i8] }

@alloc34 = private unnamed_addr constant <{ [75 x i8] }> <{ [75 x i8] c"/rustc/02072b482a8b5357f7fb5e5637444ae30e423c40/library/core/src/ptr/mod.rs" }>, align 1
@alloc35 = private unnamed_addr constant <{ i8*, [16 x i8] }> <{ i8* getelementptr inbounds (<{ [75 x i8] }>, <{ [75 x i8] }>* @alloc34, i32 0, i32 0, i32 0), [16 x i8] c"K\00\00\00\00\00\00\00\BE\02\00\00\0D\00\00\00" }>, align 8
@alloc9 = private unnamed_addr constant <{ [0 x i8] }> zeroinitializer, align 1
@__rustc_debug_gdb_scripts_section__ = linkonce_odr unnamed_addr constant [34 x i8] c"\01gdb_load_rust_pretty_printers.py\00", section ".debug_gdb_scripts", align 1

define nonnull i8* @"_ZN119_$LT$core..ptr..non_null..NonNull$LT$T$GT$$u20$as$u20$core..convert..From$LT$core..ptr..unique..Unique$LT$T$GT$$GT$$GT$4from17hd2aa0243ea29611eE"(i8* nonnull %unique) unnamed_addr #0 !dbg !6 {
start:
  %_2 = call i8* @"_ZN4core3ptr6unique15Unique$LT$T$GT$6as_ptr17hface3bb698869c37E"(i8* nonnull %unique), !dbg !13
  br label %bb1, !dbg !13

bb1:                                              ; preds = %start
  %0 = call nonnull i8* @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$13new_unchecked17h160ad7413fdaae9fE"(i8* %_2), !dbg !14
  br label %bb2, !dbg !14

bb2:                                              ; preds = %bb1
  ret i8* %0, !dbg !15
}

define { i8*, i64 } @"_ZN153_$LT$core..result..Result$LT$T$C$F$GT$$u20$as$u20$core..ops..try_trait..FromResidual$LT$core..result..Result$LT$core..convert..Infallible$C$E$GT$$GT$$GT$13from_residual17h3ebb6d63a873d87dE"() unnamed_addr #0 !dbg !16 {
start:
  %0 = alloca { i8*, i64 }, align 8
  call void @"_ZN50_$LT$T$u20$as$u20$core..convert..From$LT$T$GT$$GT$4from17h7fa262259b54d400E"(), !dbg !20
  br label %bb1, !dbg !20

bb1:                                              ; preds = %start
  %1 = bitcast { i8*, i64 }* %0 to %"core::result::Result<core::ptr::non_null::NonNull<[u8]>, core::alloc::AllocError>::Err"*, !dbg !21
  %2 = bitcast %"core::result::Result<core::ptr::non_null::NonNull<[u8]>, core::alloc::AllocError>::Err"* %1 to %"core::alloc::AllocError"*, !dbg !21
  %3 = bitcast { i8*, i64 }* %0 to {}**, !dbg !21
  store {}* null, {}** %3, align 8, !dbg !21
  %4 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %0, i32 0, i32 0, !dbg !22
  %5 = load i8*, i8** %4, align 8, !dbg !22
  %6 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %0, i32 0, i32 1, !dbg !22
  %7 = load i64, i64* %6, align 8, !dbg !22
  %8 = insertvalue { i8*, i64 } undef, i8* %5, 0, !dbg !22
  %9 = insertvalue { i8*, i64 } %8, i64 %7, 1, !dbg !22
  ret { i8*, i64 } %9, !dbg !22
}

define noalias align 8 i64* @"_ZN153_$LT$core..result..Result$LT$T$C$F$GT$$u20$as$u20$core..ops..try_trait..FromResidual$LT$core..result..Result$LT$core..convert..Infallible$C$E$GT$$GT$$GT$13from_residual17hc93f3bf83ce972faE"() unnamed_addr #0 !dbg !23 {
start:
  %0 = alloca i64*, align 8
  call void @"_ZN50_$LT$T$u20$as$u20$core..convert..From$LT$T$GT$$GT$4from17h7fa262259b54d400E"(), !dbg !24
  br label %bb1, !dbg !24

bb1:                                              ; preds = %start
  %1 = bitcast i64** %0 to %"core::result::Result<alloc::boxed::Box<core::mem::maybe_uninit::MaybeUninit<Nat>>, core::alloc::AllocError>::Err"*, !dbg !25
  %2 = bitcast %"core::result::Result<alloc::boxed::Box<core::mem::maybe_uninit::MaybeUninit<Nat>>, core::alloc::AllocError>::Err"* %1 to %"core::alloc::AllocError"*, !dbg !25
  %3 = bitcast i64** %0 to {}**, !dbg !25
  store {}* null, {}** %3, align 8, !dbg !25
  %4 = load i64*, i64** %0, align 8, !dbg !26
  ret i64* %4, !dbg !26
}

define internal i64 @_ZN4core3num7nonzero12NonZeroUsize13new_unchecked17h461957c664cf98b9E(i64 %n) unnamed_addr #0 !dbg !27 {
start:
  %0 = alloca i64, align 8
  store i64 %n, i64* %0, align 8, !dbg !32
  %1 = load i64, i64* %0, align 8, !dbg !33, !range !34
  ret i64 %1, !dbg !33
}

define internal i64 @_ZN4core3num7nonzero12NonZeroUsize3get17hfde22f630c31cb7bE(i64 %self) unnamed_addr #0 !dbg !35 {
start:
  ret i64 %self, !dbg !36
}

define void @"_ZN4core3ptr102drop_in_place$LT$alloc..boxed..Box$LT$core..mem..maybe_uninit..MaybeUninit$LT$example..Nat$GT$$GT$$GT$17h0268a0cddce88eceE"(i8*** %_1) unnamed_addr #1 personality i32 (i32, i32, i64, %"unwind::libunwind::_Unwind_Exception"*, %"unwind::libunwind::_Unwind_Context"*)* @rust_eh_personality !dbg !37 {
start:
  %0 = alloca { i8*, i32 }, align 8, !dbg !39
  br label %bb3, !dbg !39

bb3:                                              ; preds = %start
  %1 = bitcast i8*** %_1 to i64**, !dbg !39
  %2 = load i64*, i64** %1, align 8, !dbg !39, !nonnull !5
  call void @_ZN5alloc5alloc8box_free17h4df5a02897cf5996E(i64* nonnull %2), !dbg !39
  br label %bb1, !dbg !39

bb4:                                              ; No predecessors!
  %3 = bitcast i8*** %_1 to i64**, !dbg !39
  %4 = load i64*, i64** %3, align 8, !dbg !39, !nonnull !5
  call void @_ZN5alloc5alloc8box_free17h4df5a02897cf5996E(i64* nonnull %4) #6, !dbg !39
  br label %bb2, !dbg !39

bb2:                                              ; preds = %bb4
  %5 = bitcast { i8*, i32 }* %0 to i8**, !dbg !39
  %6 = load i8*, i8** %5, align 8, !dbg !39
  %7 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1, !dbg !39
  %8 = load i32, i32* %7, align 8, !dbg !39
  %9 = insertvalue { i8*, i32 } undef, i8* %6, 0, !dbg !39
  %10 = insertvalue { i8*, i32 } %9, i32 %8, 1, !dbg !39
  resume { i8*, i32 } %10, !dbg !39

bb1:                                              ; preds = %bb3
  ret void, !dbg !39
}

define { [0 x i8]*, i64 } @_ZN4core3ptr24slice_from_raw_parts_mut17h6782135ffd67944dE(i8* %data, i64 %len) unnamed_addr #0 !dbg !40 {
start:
  %0 = bitcast i8* %data to {}*, !dbg !41
  br label %bb1, !dbg !47

bb1:                                              ; preds = %start
  %1 = call { [0 x i8]*, i64 } @_ZN4core3ptr8metadata18from_raw_parts_mut17heaeaa58130f96f2bE({}* %0, i64 %len), !dbg !48
  %2 = extractvalue { [0 x i8]*, i64 } %1, 0, !dbg !48
  %3 = extractvalue { [0 x i8]*, i64 } %1, 1, !dbg !48
  br label %bb2, !dbg !48

bb2:                                              ; preds = %bb1
  %4 = insertvalue { [0 x i8]*, i64 } undef, [0 x i8]* %2, 0, !dbg !49
  %5 = insertvalue { [0 x i8]*, i64 } %4, i64 %3, 1, !dbg !49
  ret { [0 x i8]*, i64 } %5, !dbg !49
}

define void @"_ZN4core3ptr33drop_in_place$LT$example..Nat$GT$17h4500bbe220c40510E"(i64** %_1) unnamed_addr #1 !dbg !50 {
start:
  %0 = bitcast i64** %_1 to {}**, !dbg !51
  %1 = load {}*, {}** %0, align 8, !dbg !51
  %2 = icmp eq {}* %1, null, !dbg !51
  %_2 = select i1 %2, i64 0, i64 1, !dbg !51
  %3 = icmp eq i64 %_2, 0, !dbg !51
  br i1 %3, label %bb1, label %bb2, !dbg !51

bb1:                                              ; preds = %bb2, %start
  ret void, !dbg !51

bb2:                                              ; preds = %start
  %4 = bitcast i64** %_1 to i64***, !dbg !51
  call void @"_ZN4core3ptr58drop_in_place$LT$alloc..boxed..Box$LT$example..Nat$GT$$GT$17hf91bf34719c4363dE"(i64*** %4), !dbg !51
  br label %bb1, !dbg !51
}

define void @_ZN4core3ptr4read17h8d527a36feb68ea4E(%"alloc::alloc::Global"* %src) unnamed_addr #0 !dbg !52 {
start:
  %0 = alloca %"core::mem::maybe_uninit::MaybeUninit<alloc::alloc::Global>", align 1
  %tmp = alloca %"core::mem::maybe_uninit::MaybeUninit<alloc::alloc::Global>", align 1
  %1 = bitcast %"core::mem::maybe_uninit::MaybeUninit<alloc::alloc::Global>"* %0 to {}*, !dbg !53
  br label %bb1, !dbg !60

bb1:                                              ; preds = %start
  %2 = bitcast %"core::mem::maybe_uninit::MaybeUninit<alloc::alloc::Global>"* %tmp to %"alloc::alloc::Global"*, !dbg !61
  br label %bb2, !dbg !64

bb2:                                              ; preds = %bb1
  %3 = bitcast %"alloc::alloc::Global"* %2 to i8*, !dbg !65
  %4 = bitcast %"alloc::alloc::Global"* %src to i8*, !dbg !65
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 1 %3, i8* align 1 %4, i64 0, i1 false), !dbg !65
  br label %bb3, !dbg !66

bb3:                                              ; preds = %bb2
  ret void, !dbg !67
}

define void @"_ZN4core3ptr56drop_in_place$LT$example..Vector$LT$example..Nat$GT$$GT$17h86962fbc7676f71eE"(%"Vector<Nat>"* %_1) unnamed_addr #1 personality i32 (i32, i32, i64, %"unwind::libunwind::_Unwind_Exception"*, %"unwind::libunwind::_Unwind_Context"*)* @rust_eh_personality !dbg !68 {
start:
  %0 = alloca { i8*, i32 }, align 8, !dbg !69
  %1 = getelementptr inbounds %"Vector<Nat>", %"Vector<Nat>"* %_1, i32 0, i32 1, !dbg !69
  %2 = load {}*, {}** %1, align 8, !dbg !69
  %3 = icmp eq {}* %2, null, !dbg !69
  %_2 = select i1 %3, i64 0, i64 1, !dbg !69
  %4 = icmp eq i64 %_2, 0, !dbg !69
  br i1 %4, label %bb2, label %bb7, !dbg !69

bb2:                                              ; preds = %bb5, %start
  ret void, !dbg !69

bb7:                                              ; preds = %start
  %5 = bitcast %"Vector<Nat>"* %_1 to %"Vector<Nat>::Cons"*, !dbg !69
  %6 = bitcast %"Vector<Nat>::Cons"* %5 to i64**, !dbg !69
  invoke void @"_ZN4core3ptr33drop_in_place$LT$example..Nat$GT$17h4500bbe220c40510E"(i64** %6)
          to label %bb6 unwind label %cleanup, !dbg !69

bb6:                                              ; preds = %bb7
  %7 = bitcast %"Vector<Nat>"* %_1 to %"Vector<Nat>::Cons"*, !dbg !69
  %8 = getelementptr inbounds %"Vector<Nat>::Cons", %"Vector<Nat>::Cons"* %7, i32 0, i32 1, !dbg !69
  invoke void @"_ZN4core3ptr33drop_in_place$LT$example..Nat$GT$17h4500bbe220c40510E"(i64** %8)
          to label %bb5 unwind label %cleanup1, !dbg !69

bb4:                                              ; preds = %cleanup
  %9 = bitcast %"Vector<Nat>"* %_1 to %"Vector<Nat>::Cons"*, !dbg !69
  %10 = getelementptr inbounds %"Vector<Nat>::Cons", %"Vector<Nat>::Cons"* %9, i32 0, i32 1, !dbg !69
  call void @"_ZN4core3ptr33drop_in_place$LT$example..Nat$GT$17h4500bbe220c40510E"(i64** %10) #6, !dbg !69
  br label %bb3, !dbg !69

cleanup:                                          ; preds = %bb7
  %11 = landingpad { i8*, i32 }
          cleanup
  %12 = extractvalue { i8*, i32 } %11, 0
  %13 = extractvalue { i8*, i32 } %11, 1
  %14 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 0
  store i8* %12, i8** %14, align 8
  %15 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1
  store i32 %13, i32* %15, align 8
  br label %bb4

bb3:                                              ; preds = %cleanup1, %bb4
  %16 = bitcast %"Vector<Nat>"* %_1 to %"Vector<Nat>::Cons"*, !dbg !69
  %17 = getelementptr inbounds %"Vector<Nat>::Cons", %"Vector<Nat>::Cons"* %16, i32 0, i32 2, !dbg !69
  call void @"_ZN4core3ptr81drop_in_place$LT$alloc..boxed..Box$LT$example..Vector$LT$example..Nat$GT$$GT$$GT$17h1fec5106381daebfE"(%"Vector<Nat>"** %17) #6, !dbg !69
  br label %bb1, !dbg !69

bb5:                                              ; preds = %bb6
  %18 = bitcast %"Vector<Nat>"* %_1 to %"Vector<Nat>::Cons"*, !dbg !69
  %19 = getelementptr inbounds %"Vector<Nat>::Cons", %"Vector<Nat>::Cons"* %18, i32 0, i32 2, !dbg !69
  call void @"_ZN4core3ptr81drop_in_place$LT$alloc..boxed..Box$LT$example..Vector$LT$example..Nat$GT$$GT$$GT$17h1fec5106381daebfE"(%"Vector<Nat>"** %19), !dbg !69
  br label %bb2, !dbg !69

cleanup1:                                         ; preds = %bb6
  %20 = landingpad { i8*, i32 }
          cleanup
  %21 = extractvalue { i8*, i32 } %20, 0
  %22 = extractvalue { i8*, i32 } %20, 1
  %23 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 0
  store i8* %21, i8** %23, align 8
  %24 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1
  store i32 %22, i32* %24, align 8
  br label %bb3

bb1:                                              ; preds = %bb3
  %25 = bitcast { i8*, i32 }* %0 to i8**, !dbg !69
  %26 = load i8*, i8** %25, align 8, !dbg !69
  %27 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1, !dbg !69
  %28 = load i32, i32* %27, align 8, !dbg !69
  %29 = insertvalue { i8*, i32 } undef, i8* %26, 0, !dbg !69
  %30 = insertvalue { i8*, i32 } %29, i32 %28, 1, !dbg !69
  resume { i8*, i32 } %30, !dbg !69
}

define void @"_ZN4core3ptr58drop_in_place$LT$alloc..boxed..Box$LT$example..Nat$GT$$GT$17hf91bf34719c4363dE"(i64*** %_1) unnamed_addr #1 personality i32 (i32, i32, i64, %"unwind::libunwind::_Unwind_Exception"*, %"unwind::libunwind::_Unwind_Context"*)* @rust_eh_personality !dbg !70 {
start:
  %0 = alloca { i8*, i32 }, align 8, !dbg !71
  %1 = load i64**, i64*** %_1, align 8, !dbg !71, !nonnull !5
  invoke void @"_ZN4core3ptr33drop_in_place$LT$example..Nat$GT$17h4500bbe220c40510E"(i64** %1)
          to label %bb3 unwind label %cleanup, !dbg !71

bb3:                                              ; preds = %start
  %2 = bitcast i64*** %_1 to i64**, !dbg !71
  %3 = load i64*, i64** %2, align 8, !dbg !71, !nonnull !5
  call void @_ZN5alloc5alloc8box_free17h75d3a0df5b182abcE(i64* nonnull %3), !dbg !71
  br label %bb1, !dbg !71

bb4:                                              ; preds = %cleanup
  %4 = bitcast i64*** %_1 to i64**, !dbg !71
  %5 = load i64*, i64** %4, align 8, !dbg !71, !nonnull !5
  call void @_ZN5alloc5alloc8box_free17h75d3a0df5b182abcE(i64* nonnull %5) #6, !dbg !71
  br label %bb2, !dbg !71

cleanup:                                          ; preds = %start
  %6 = landingpad { i8*, i32 }
          cleanup
  %7 = extractvalue { i8*, i32 } %6, 0
  %8 = extractvalue { i8*, i32 } %6, 1
  %9 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 0
  store i8* %7, i8** %9, align 8
  %10 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1
  store i32 %8, i32* %10, align 8
  br label %bb4

bb2:                                              ; preds = %bb4
  %11 = bitcast { i8*, i32 }* %0 to i8**, !dbg !71
  %12 = load i8*, i8** %11, align 8, !dbg !71
  %13 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1, !dbg !71
  %14 = load i32, i32* %13, align 8, !dbg !71
  %15 = insertvalue { i8*, i32 } undef, i8* %12, 0, !dbg !71
  %16 = insertvalue { i8*, i32 } %15, i32 %14, 1, !dbg !71
  resume { i8*, i32 } %16, !dbg !71

bb1:                                              ; preds = %bb3
  ret void, !dbg !71
}

define void @_ZN4core3ptr5write17h72a939caa164f97bE(i64** %dst, i64* noalias align 8 %0) unnamed_addr #0 !dbg !72 {
start:
  %src = alloca i64*, align 8
  store i64* %0, i64** %src, align 8
  %1 = bitcast i64** %dst to i8*, !dbg !73
  %2 = bitcast i64** %src to i8*, !dbg !73
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %1, i8* align 8 %2, i64 8, i1 false), !dbg !73
  ret void, !dbg !74
}

define nonnull i8* @"_ZN4core3ptr6unique15Unique$LT$T$GT$13new_unchecked17h4fc1880c9e391d78E"(i8* %ptr) unnamed_addr #0 !dbg !75 {
start:
  %0 = alloca i8*, align 8
  store i8* %ptr, i8** %0, align 8, !dbg !79
  %1 = load i8*, i8** %0, align 8, !dbg !80, !nonnull !5
  ret i8* %1, !dbg !80
}

define nonnull i64* @"_ZN4core3ptr6unique15Unique$LT$T$GT$13new_unchecked17h52e4cab5bec4cf56E"(i64** %ptr) unnamed_addr #0 !dbg !81 {
start:
  %0 = alloca i64*, align 8
  %1 = bitcast i64** %0 to i64***, !dbg !82
  store i64** %ptr, i64*** %1, align 8, !dbg !82
  %2 = load i64*, i64** %0, align 8, !dbg !83, !nonnull !5
  ret i64* %2, !dbg !83
}

define nonnull i64* @"_ZN4core3ptr6unique15Unique$LT$T$GT$13new_unchecked17hf5d39441e41f2a4fE"(i8** %ptr) unnamed_addr #0 !dbg !84 {
start:
  %0 = alloca i64*, align 8
  %1 = bitcast i64** %0 to i8***, !dbg !85
  store i8** %ptr, i8*** %1, align 8, !dbg !85
  %2 = load i64*, i64** %0, align 8, !dbg !86, !nonnull !5
  ret i64* %2, !dbg !86
}

define nonnull i8* @"_ZN4core3ptr6unique15Unique$LT$T$GT$4cast17h1f55cacfc2510c05E"(i64* nonnull %self) unnamed_addr #0 !dbg !87 {
start:
  %_3 = call %"Vector<Nat>"* @"_ZN4core3ptr6unique15Unique$LT$T$GT$6as_ptr17ha4c2d95dfd297bbfE"(i64* nonnull %self), !dbg !88
  br label %bb1, !dbg !88

bb1:                                              ; preds = %start
  %_2 = bitcast %"Vector<Nat>"* %_3 to i8*, !dbg !88
  %0 = call nonnull i8* @"_ZN4core3ptr6unique15Unique$LT$T$GT$13new_unchecked17h4fc1880c9e391d78E"(i8* %_2), !dbg !89
  br label %bb2, !dbg !89

bb2:                                              ; preds = %bb1
  ret i8* %0, !dbg !90
}

define nonnull i8* @"_ZN4core3ptr6unique15Unique$LT$T$GT$4cast17h8efa5f9215b55e0cE"(i64* nonnull %self) unnamed_addr #0 !dbg !91 {
start:
  %_3 = call i64** @"_ZN4core3ptr6unique15Unique$LT$T$GT$6as_ptr17h68ca818130bbc41cE"(i64* nonnull %self), !dbg !92
  br label %bb1, !dbg !92

bb1:                                              ; preds = %start
  %_2 = bitcast i64** %_3 to i8*, !dbg !92
  %0 = call nonnull i8* @"_ZN4core3ptr6unique15Unique$LT$T$GT$13new_unchecked17h4fc1880c9e391d78E"(i8* %_2), !dbg !93
  br label %bb2, !dbg !93

bb2:                                              ; preds = %bb1
  ret i8* %0, !dbg !94
}

define nonnull i8* @"_ZN4core3ptr6unique15Unique$LT$T$GT$4cast17hf9fab5d337fb7077E"(i64* nonnull %self) unnamed_addr #0 !dbg !95 {
start:
  %_3 = call i8** @"_ZN4core3ptr6unique15Unique$LT$T$GT$6as_ptr17h91f3760617147a77E"(i64* nonnull %self), !dbg !96
  br label %bb1, !dbg !96

bb1:                                              ; preds = %start
  %_2 = bitcast i8** %_3 to i8*, !dbg !96
  %0 = call nonnull i8* @"_ZN4core3ptr6unique15Unique$LT$T$GT$13new_unchecked17h4fc1880c9e391d78E"(i8* %_2), !dbg !97
  br label %bb2, !dbg !97

bb2:                                              ; preds = %bb1
  ret i8* %0, !dbg !98
}

define i64** @"_ZN4core3ptr6unique15Unique$LT$T$GT$6as_ptr17h68ca818130bbc41cE"(i64* nonnull %self) unnamed_addr #0 !dbg !99 {
start:
  %_2 = bitcast i64* %self to i64**, !dbg !100
  ret i64** %_2, !dbg !101
}

define i8** @"_ZN4core3ptr6unique15Unique$LT$T$GT$6as_ptr17h91f3760617147a77E"(i64* nonnull %self) unnamed_addr #0 !dbg !102 {
start:
  %_2 = bitcast i64* %self to i8**, !dbg !103
  ret i8** %_2, !dbg !104
}

define %"Vector<Nat>"* @"_ZN4core3ptr6unique15Unique$LT$T$GT$6as_ptr17ha4c2d95dfd297bbfE"(i64* nonnull %self) unnamed_addr #0 !dbg !105 {
start:
  %_2 = bitcast i64* %self to %"Vector<Nat>"*, !dbg !106
  ret %"Vector<Nat>"* %_2, !dbg !107
}

define i8* @"_ZN4core3ptr6unique15Unique$LT$T$GT$6as_ptr17hface3bb698869c37E"(i8* nonnull %self) unnamed_addr #0 !dbg !108 {
start:
  ret i8* %self, !dbg !109
}

define align 8 dereferenceable(8) i8** @"_ZN4core3ptr6unique15Unique$LT$T$GT$6as_ref17h6a184e1ed3728056E"(i64** align 8 dereferenceable(8) %self) unnamed_addr #0 !dbg !110 {
start:
  %_3 = load i64*, i64** %self, align 8, !dbg !111, !nonnull !5
  %_2 = call i8** @"_ZN4core3ptr6unique15Unique$LT$T$GT$6as_ptr17h91f3760617147a77E"(i64* nonnull %_3), !dbg !111
  br label %bb1, !dbg !111

bb1:                                              ; preds = %start
  ret i8** %_2, !dbg !112
}

define align 8 dereferenceable(8) i64** @"_ZN4core3ptr6unique15Unique$LT$T$GT$6as_ref17h8acdb05c0d378c35E"(i64** align 8 dereferenceable(8) %self) unnamed_addr #0 !dbg !113 {
start:
  %_3 = load i64*, i64** %self, align 8, !dbg !114, !nonnull !5
  %_2 = call i64** @"_ZN4core3ptr6unique15Unique$LT$T$GT$6as_ptr17h68ca818130bbc41cE"(i64* nonnull %_3), !dbg !114
  br label %bb1, !dbg !114

bb1:                                              ; preds = %start
  ret i64** %_2, !dbg !115
}

define align 8 dereferenceable(24) %"Vector<Nat>"* @"_ZN4core3ptr6unique15Unique$LT$T$GT$6as_ref17he5982509a295a41bE"(i64** align 8 dereferenceable(8) %self) unnamed_addr #0 !dbg !116 {
start:
  %_3 = load i64*, i64** %self, align 8, !dbg !117, !nonnull !5
  %_2 = call %"Vector<Nat>"* @"_ZN4core3ptr6unique15Unique$LT$T$GT$6as_ptr17ha4c2d95dfd297bbfE"(i64* nonnull %_3), !dbg !117
  br label %bb1, !dbg !117

bb1:                                              ; preds = %start
  ret %"Vector<Nat>"* %_2, !dbg !118
}

define zeroext i1 @"_ZN4core3ptr7mut_ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$13guaranteed_eq17h7471bd417ff574a5E"(i8* %self, i8* %other) unnamed_addr #0 !dbg !119 {
start:
  %0 = alloca i8, align 1
  %1 = icmp eq i8* %self, %other, !dbg !120
  %2 = zext i1 %1 to i8, !dbg !120
  store i8 %2, i8* %0, align 1, !dbg !120
  %3 = load i8, i8* %0, align 1, !dbg !120, !range !121
  %4 = trunc i8 %3 to i1, !dbg !120
  br label %bb1, !dbg !120

bb1:                                              ; preds = %start
  ret i1 %4, !dbg !122
}

define zeroext i1 @"_ZN4core3ptr7mut_ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$7is_null17h08fdce2fa73f9438E"(i8* %self) unnamed_addr #0 !dbg !123 {
start:
  br label %bb1, !dbg !124

bb1:                                              ; preds = %start
  %0 = call zeroext i1 @"_ZN4core3ptr7mut_ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$13guaranteed_eq17h7471bd417ff574a5E"(i8* %self, i8* null), !dbg !125
  br label %bb2, !dbg !125

bb2:                                              ; preds = %bb1
  ret i1 %0, !dbg !126
}

define void @"_ZN4core3ptr81drop_in_place$LT$alloc..boxed..Box$LT$example..Vector$LT$example..Nat$GT$$GT$$GT$17h1fec5106381daebfE"(%"Vector<Nat>"** %_1) unnamed_addr #1 personality i32 (i32, i32, i64, %"unwind::libunwind::_Unwind_Exception"*, %"unwind::libunwind::_Unwind_Context"*)* @rust_eh_personality !dbg !127 {
start:
  %0 = alloca { i8*, i32 }, align 8, !dbg !128
  %1 = load %"Vector<Nat>"*, %"Vector<Nat>"** %_1, align 8, !dbg !128, !nonnull !5
  invoke void @"_ZN4core3ptr56drop_in_place$LT$example..Vector$LT$example..Nat$GT$$GT$17h86962fbc7676f71eE"(%"Vector<Nat>"* %1)
          to label %bb3 unwind label %cleanup, !dbg !128

bb3:                                              ; preds = %start
  %2 = bitcast %"Vector<Nat>"** %_1 to i64**, !dbg !128
  %3 = load i64*, i64** %2, align 8, !dbg !128, !nonnull !5
  call void @_ZN5alloc5alloc8box_free17h487859dd7008df07E(i64* nonnull %3), !dbg !128
  br label %bb1, !dbg !128

bb4:                                              ; preds = %cleanup
  %4 = bitcast %"Vector<Nat>"** %_1 to i64**, !dbg !128
  %5 = load i64*, i64** %4, align 8, !dbg !128, !nonnull !5
  call void @_ZN5alloc5alloc8box_free17h487859dd7008df07E(i64* nonnull %5) #6, !dbg !128
  br label %bb2, !dbg !128

cleanup:                                          ; preds = %start
  %6 = landingpad { i8*, i32 }
          cleanup
  %7 = extractvalue { i8*, i32 } %6, 0
  %8 = extractvalue { i8*, i32 } %6, 1
  %9 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 0
  store i8* %7, i8** %9, align 8
  %10 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1
  store i32 %8, i32* %10, align 8
  br label %bb4

bb2:                                              ; preds = %bb4
  %11 = bitcast { i8*, i32 }* %0 to i8**, !dbg !128
  %12 = load i8*, i8** %11, align 8, !dbg !128
  %13 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1, !dbg !128
  %14 = load i32, i32* %13, align 8, !dbg !128
  %15 = insertvalue { i8*, i32 } undef, i8* %12, 0, !dbg !128
  %16 = insertvalue { i8*, i32 } %15, i32 %14, 1, !dbg !128
  resume { i8*, i32 } %16, !dbg !128

bb1:                                              ; preds = %bb3
  ret void, !dbg !128
}

define { [0 x i8]*, i64 } @_ZN4core3ptr8metadata18from_raw_parts_mut17heaeaa58130f96f2bE({}* %data_address, i64 %metadata) unnamed_addr #0 !dbg !129 {
start:
  %_4 = alloca { i8*, i64 }, align 8
  %_3 = alloca %"core::ptr::metadata::PtrRepr<[u8]>", align 8
  %0 = bitcast { i8*, i64 }* %_4 to {}**, !dbg !132
  store {}* %data_address, {}** %0, align 8, !dbg !132
  %1 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %_4, i32 0, i32 1, !dbg !132
  store i64 %metadata, i64* %1, align 8, !dbg !132
  %2 = bitcast %"core::ptr::metadata::PtrRepr<[u8]>"* %_3 to { i8*, i64 }*, !dbg !133
  %3 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %_4, i32 0, i32 0, !dbg !133
  %4 = load i8*, i8** %3, align 8, !dbg !133
  %5 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %_4, i32 0, i32 1, !dbg !133
  %6 = load i64, i64* %5, align 8, !dbg !133
  %7 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %2, i32 0, i32 0, !dbg !133
  store i8* %4, i8** %7, align 8, !dbg !133
  %8 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %2, i32 0, i32 1, !dbg !133
  store i64 %6, i64* %8, align 8, !dbg !133
  %9 = bitcast %"core::ptr::metadata::PtrRepr<[u8]>"* %_3 to { [0 x i8]*, i64 }*, !dbg !133
  %10 = getelementptr inbounds { [0 x i8]*, i64 }, { [0 x i8]*, i64 }* %9, i32 0, i32 0, !dbg !133
  %11 = load [0 x i8]*, [0 x i8]** %10, align 8, !dbg !133
  %12 = getelementptr inbounds { [0 x i8]*, i64 }, { [0 x i8]*, i64 }* %9, i32 0, i32 1, !dbg !133
  %13 = load i64, i64* %12, align 8, !dbg !133
  %14 = insertvalue { [0 x i8]*, i64 } undef, [0 x i8]* %11, 0, !dbg !134
  %15 = insertvalue { [0 x i8]*, i64 } %14, i64 %13, 1, !dbg !134
  ret { [0 x i8]*, i64 } %15, !dbg !134
}

define nonnull i8* @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$13new_unchecked17h160ad7413fdaae9fE"(i8* %ptr) unnamed_addr #0 !dbg !135 {
start:
  %0 = alloca i8*, align 8
  store i8* %ptr, i8** %0, align 8, !dbg !137
  %1 = load i8*, i8** %0, align 8, !dbg !138, !nonnull !5
  ret i8* %1, !dbg !138
}

define { i8*, i64 } @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$13new_unchecked17h22a1eade97401e19E"([0 x i8]* %ptr.0, i64 %ptr.1) unnamed_addr #0 !dbg !139 {
start:
  %0 = alloca { i8*, i64 }, align 8
  %1 = bitcast { i8*, i64 }* %0 to { [0 x i8]*, i64 }*, !dbg !140
  %2 = getelementptr inbounds { [0 x i8]*, i64 }, { [0 x i8]*, i64 }* %1, i32 0, i32 0, !dbg !140
  store [0 x i8]* %ptr.0, [0 x i8]** %2, align 8, !dbg !140
  %3 = getelementptr inbounds { [0 x i8]*, i64 }, { [0 x i8]*, i64 }* %1, i32 0, i32 1, !dbg !140
  store i64 %ptr.1, i64* %3, align 8, !dbg !140
  %4 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %0, i32 0, i32 0, !dbg !141
  %5 = load i8*, i8** %4, align 8, !dbg !141, !nonnull !5
  %6 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %0, i32 0, i32 1, !dbg !141
  %7 = load i64, i64* %6, align 8, !dbg !141
  %8 = insertvalue { i8*, i64 } undef, i8* %5, 0, !dbg !141
  %9 = insertvalue { i8*, i64 } %8, i64 %7, 1, !dbg !141
  ret { i8*, i64 } %9, !dbg !141
}

define nonnull i64* @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$13new_unchecked17h89edd023daa903eeE"(i8** %ptr) unnamed_addr #0 !dbg !142 {
start:
  %0 = alloca i64*, align 8
  %1 = bitcast i64** %0 to i8***, !dbg !143
  store i8** %ptr, i8*** %1, align 8, !dbg !143
  %2 = load i64*, i64** %0, align 8, !dbg !144, !nonnull !5
  ret i64* %2, !dbg !144
}

define i8* @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$3new17hebae0b2290bdef64E"(i8* %ptr) unnamed_addr #0 !dbg !145 {
start:
  %0 = alloca i8*, align 8
  %_3 = call zeroext i1 @"_ZN4core3ptr7mut_ptr31_$LT$impl$u20$$BP$mut$u20$T$GT$7is_null17h08fdce2fa73f9438E"(i8* %ptr), !dbg !146
  br label %bb1, !dbg !146

bb1:                                              ; preds = %start
  %_2 = xor i1 %_3, true, !dbg !147
  br i1 %_2, label %bb2, label %bb4, !dbg !147

bb4:                                              ; preds = %bb1
  %1 = bitcast i8** %0 to {}**, !dbg !148
  store {}* null, {}** %1, align 8, !dbg !148
  br label %bb5, !dbg !149

bb2:                                              ; preds = %bb1
  %_5 = call nonnull i8* @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$13new_unchecked17h160ad7413fdaae9fE"(i8* %ptr), !dbg !150
  br label %bb3, !dbg !150

bb3:                                              ; preds = %bb2
  store i8* %_5, i8** %0, align 8, !dbg !151
  br label %bb5, !dbg !149

bb5:                                              ; preds = %bb4, %bb3
  %2 = load i8*, i8** %0, align 8, !dbg !152
  ret i8* %2, !dbg !152
}

define nonnull i64* @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$4cast17h052232ae0084c658E"(i8* nonnull %self.0, i64 %self.1) unnamed_addr #0 !dbg !153 {
start:
  %0 = call { [0 x i8]*, i64 } @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$6as_ptr17h8d9d7e25c6b333f7E"(i8* nonnull %self.0, i64 %self.1), !dbg !154
  %_3.0 = extractvalue { [0 x i8]*, i64 } %0, 0, !dbg !154
  %_3.1 = extractvalue { [0 x i8]*, i64 } %0, 1, !dbg !154
  br label %bb1, !dbg !154

bb1:                                              ; preds = %start
  %_2 = bitcast [0 x i8]* %_3.0 to i8**, !dbg !154
  %1 = call nonnull i64* @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$13new_unchecked17h89edd023daa903eeE"(i8** %_2), !dbg !155
  br label %bb2, !dbg !155

bb2:                                              ; preds = %bb1
  ret i64* %1, !dbg !156
}

define i8** @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$6as_ptr17h374e705f028538d8E"(i64* nonnull %self) unnamed_addr #0 !dbg !157 {
start:
  %_2 = bitcast i64* %self to i8**, !dbg !158
  ret i8** %_2, !dbg !159
}

define i8* @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$6as_ptr17h42c4b7e5250d107bE"(i8* nonnull %self) unnamed_addr #0 !dbg !160 {
start:
  ret i8* %self, !dbg !161
}

define { [0 x i8]*, i64 } @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$6as_ptr17h8d9d7e25c6b333f7E"(i8* nonnull %self.0, i64 %self.1) unnamed_addr #0 !dbg !162 {
start:
  %_2.0 = bitcast i8* %self.0 to [0 x i8]*, !dbg !163
  %0 = insertvalue { [0 x i8]*, i64 } undef, [0 x i8]* %_2.0, 0, !dbg !164
  %1 = insertvalue { [0 x i8]*, i64 } %0, i64 %self.1, 1, !dbg !164
  ret { [0 x i8]*, i64 } %1, !dbg !164
}

define i8* @"_ZN4core3ptr8non_null26NonNull$LT$$u5b$T$u5d$$GT$10as_mut_ptr17h86097296280f5b0dE"(i8* nonnull %self.0, i64 %self.1) unnamed_addr #0 !dbg !165 {
start:
  %_2 = call nonnull i8* @"_ZN4core3ptr8non_null26NonNull$LT$$u5b$T$u5d$$GT$15as_non_null_ptr17h7c8d99f52e6d5446E"(i8* nonnull %self.0, i64 %self.1), !dbg !166
  br label %bb1, !dbg !166

bb1:                                              ; preds = %start
  %0 = call i8* @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$6as_ptr17h42c4b7e5250d107bE"(i8* nonnull %_2), !dbg !166
  br label %bb2, !dbg !166

bb2:                                              ; preds = %bb1
  ret i8* %0, !dbg !167
}

define nonnull i8* @"_ZN4core3ptr8non_null26NonNull$LT$$u5b$T$u5d$$GT$15as_non_null_ptr17h7c8d99f52e6d5446E"(i8* nonnull %self.0, i64 %self.1) unnamed_addr #0 !dbg !168 {
start:
  %0 = call { [0 x i8]*, i64 } @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$6as_ptr17h8d9d7e25c6b333f7E"(i8* nonnull %self.0, i64 %self.1), !dbg !169
  %_3.0 = extractvalue { [0 x i8]*, i64 } %0, 0, !dbg !169
  %_3.1 = extractvalue { [0 x i8]*, i64 } %0, 1, !dbg !169
  br label %bb1, !dbg !169

bb1:                                              ; preds = %start
  %1 = bitcast [0 x i8]* %_3.0 to i8*, !dbg !170
  br label %bb2, !dbg !169

bb2:                                              ; preds = %bb1
  %2 = call nonnull i8* @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$13new_unchecked17h160ad7413fdaae9fE"(i8* %1), !dbg !174
  br label %bb3, !dbg !174

bb3:                                              ; preds = %bb2
  ret i8* %2, !dbg !175
}

define { i8*, i64 } @"_ZN4core3ptr8non_null26NonNull$LT$$u5b$T$u5d$$GT$20slice_from_raw_parts17hbd76d94f6ce21ba6E"(i8* nonnull %data, i64 %len) unnamed_addr #0 !dbg !176 {
start:
  %_4 = call i8* @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$6as_ptr17h42c4b7e5250d107bE"(i8* nonnull %data), !dbg !177
  br label %bb1, !dbg !177

bb1:                                              ; preds = %start
  %0 = call { [0 x i8]*, i64 } @_ZN4core3ptr24slice_from_raw_parts_mut17h6782135ffd67944dE(i8* %_4, i64 %len), !dbg !178
  %_3.0 = extractvalue { [0 x i8]*, i64 } %0, 0, !dbg !178
  %_3.1 = extractvalue { [0 x i8]*, i64 } %0, 1, !dbg !178
  br label %bb2, !dbg !178

bb2:                                              ; preds = %bb1
  %1 = call { i8*, i64 } @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$13new_unchecked17h22a1eade97401e19E"([0 x i8]* %_3.0, i64 %_3.1), !dbg !179
  %2 = extractvalue { i8*, i64 } %1, 0, !dbg !179
  %3 = extractvalue { i8*, i64 } %1, 1, !dbg !179
  br label %bb3, !dbg !179

bb3:                                              ; preds = %bb2
  %4 = insertvalue { i8*, i64 } undef, i8* %2, 0, !dbg !180
  %5 = insertvalue { i8*, i64 } %4, i64 %3, 1, !dbg !180
  ret { i8*, i64 } %5, !dbg !180
}

define { i64, i64 } @_ZN4core5alloc6layout10size_align17h2fa81a1885879a38E() unnamed_addr #1 !dbg !181 {
start:
  %0 = alloca { i64, i64 }, align 8
  br label %bb1, !dbg !185

bb1:                                              ; preds = %start
  br label %bb2, !dbg !186

bb2:                                              ; preds = %bb1
  %1 = bitcast { i64, i64 }* %0 to i64*, !dbg !187
  store i64 8, i64* %1, align 8, !dbg !187
  %2 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %0, i32 0, i32 1, !dbg !187
  store i64 8, i64* %2, align 8, !dbg !187
  %3 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %0, i32 0, i32 0, !dbg !188
  %4 = load i64, i64* %3, align 8, !dbg !188
  %5 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %0, i32 0, i32 1, !dbg !188
  %6 = load i64, i64* %5, align 8, !dbg !188
  %7 = insertvalue { i64, i64 } undef, i64 %4, 0, !dbg !188
  %8 = insertvalue { i64, i64 } %7, i64 %6, 1, !dbg !188
  ret { i64, i64 } %8, !dbg !188
}

define internal { i64, i64 } @_ZN4core5alloc6layout6Layout25from_size_align_unchecked17h864fda2504d46fd7E(i64 %size, i64 %align) unnamed_addr #0 !dbg !189 {
start:
  %0 = alloca { i64, i64 }, align 8
  %_4 = call i64 @_ZN4core3num7nonzero12NonZeroUsize13new_unchecked17h461957c664cf98b9E(i64 %align), !dbg !191, !range !34
  br label %bb1, !dbg !191

bb1:                                              ; preds = %start
  %1 = bitcast { i64, i64 }* %0 to i64*, !dbg !192
  store i64 %size, i64* %1, align 8, !dbg !192
  %2 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %0, i32 0, i32 1, !dbg !192
  store i64 %_4, i64* %2, align 8, !dbg !192
  %3 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %0, i32 0, i32 0, !dbg !193
  %4 = load i64, i64* %3, align 8, !dbg !193
  %5 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %0, i32 0, i32 1, !dbg !193
  %6 = load i64, i64* %5, align 8, !dbg !193, !range !34
  %7 = insertvalue { i64, i64 } undef, i64 %4, 0, !dbg !193
  %8 = insertvalue { i64, i64 } %7, i64 %6, 1, !dbg !193
  ret { i64, i64 } %8, !dbg !193
}

define { i64, i64 } @_ZN4core5alloc6layout6Layout3new17hbb5ff3defbc8cbc0E() unnamed_addr #0 !dbg !194 {
start:
  %0 = call { i64, i64 } @_ZN4core5alloc6layout10size_align17h2fa81a1885879a38E(), !dbg !195
  %_3.0 = extractvalue { i64, i64 } %0, 0, !dbg !195
  %_3.1 = extractvalue { i64, i64 } %0, 1, !dbg !195
  br label %bb1, !dbg !195

bb1:                                              ; preds = %start
  %1 = call { i64, i64 } @_ZN4core5alloc6layout6Layout25from_size_align_unchecked17h864fda2504d46fd7E(i64 %_3.0, i64 %_3.1), !dbg !196
  %2 = extractvalue { i64, i64 } %1, 0, !dbg !196
  %3 = extractvalue { i64, i64 } %1, 1, !dbg !196
  br label %bb2, !dbg !196

bb2:                                              ; preds = %bb1
  %4 = insertvalue { i64, i64 } undef, i64 %2, 0, !dbg !197
  %5 = insertvalue { i64, i64 } %4, i64 %3, 1, !dbg !197
  ret { i64, i64 } %5, !dbg !197
}

define internal i64 @_ZN4core5alloc6layout6Layout4size17h1aa94a8afe68f159E({ i64, i64 }* align 8 dereferenceable(16) %self) unnamed_addr #0 !dbg !198 {
start:
  %0 = bitcast { i64, i64 }* %self to i64*, !dbg !199
  %1 = load i64, i64* %0, align 8, !dbg !199
  ret i64 %1, !dbg !200
}

define internal i64 @_ZN4core5alloc6layout6Layout5align17hda36d11e4adac4adE({ i64, i64 }* align 8 dereferenceable(16) %self) unnamed_addr #0 !dbg !201 {
start:
  %0 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %self, i32 0, i32 1, !dbg !202
  %_2 = load i64, i64* %0, align 8, !dbg !202, !range !34
  %1 = call i64 @_ZN4core3num7nonzero12NonZeroUsize3get17hfde22f630c31cb7bE(i64 %_2), !dbg !202
  br label %bb1, !dbg !202

bb1:                                              ; preds = %start
  ret i64 %1, !dbg !203
}

define internal nonnull i8* @_ZN4core5alloc6layout6Layout8dangling17h5e2014c69dca2d07E({ i64, i64 }* align 8 dereferenceable(16) %self) unnamed_addr #0 !dbg !204 {
start:
  %_3 = call i64 @_ZN4core5alloc6layout6Layout5align17hda36d11e4adac4adE({ i64, i64 }* align 8 dereferenceable(16) %self), !dbg !205
  br label %bb1, !dbg !205

bb1:                                              ; preds = %start
  %_2 = inttoptr i64 %_3 to i8*, !dbg !205
  %0 = call nonnull i8* @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$13new_unchecked17h160ad7413fdaae9fE"(i8* %_2), !dbg !206
  br label %bb2, !dbg !206

bb2:                                              ; preds = %bb1
  ret i8* %0, !dbg !207
}

define i8* @"_ZN4core6option15Option$LT$T$GT$5ok_or17h864498eacc8aacb9E"(i8* %0) unnamed_addr #0 !dbg !208 {
start:
  %_7 = alloca i8, align 1
  %1 = alloca i8*, align 8
  %self = alloca i8*, align 8
  store i8* %0, i8** %self, align 8
  store i8 0, i8* %_7, align 1, !dbg !212
  store i8 1, i8* %_7, align 1, !dbg !212
  %2 = bitcast i8** %self to {}**, !dbg !212
  %3 = load {}*, {}** %2, align 8, !dbg !212
  %4 = icmp eq {}* %3, null, !dbg !212
  %_3 = select i1 %4, i64 0, i64 1, !dbg !212
  switch i64 %_3, label %bb2 [
    i64 0, label %bb1
    i64 1, label %bb3
  ], !dbg !213

bb2:                                              ; preds = %start
  unreachable, !dbg !212

bb1:                                              ; preds = %start
  store i8 0, i8* %_7, align 1, !dbg !214
  %5 = bitcast i8** %1 to %"core::result::Result<core::ptr::non_null::NonNull<u8>, core::alloc::AllocError>::Err"*, !dbg !215
  %6 = bitcast %"core::result::Result<core::ptr::non_null::NonNull<u8>, core::alloc::AllocError>::Err"* %5 to %"core::alloc::AllocError"*, !dbg !215
  %7 = bitcast i8** %1 to {}**, !dbg !215
  store {}* null, {}** %7, align 8, !dbg !215
  br label %bb4, !dbg !216

bb3:                                              ; preds = %start
  %v = load i8*, i8** %self, align 8, !dbg !217, !nonnull !5
  store i8* %v, i8** %1, align 8, !dbg !218
  br label %bb4, !dbg !219

bb4:                                              ; preds = %bb1, %bb3
  %8 = load i8, i8* %_7, align 1, !dbg !220, !range !121
  %9 = trunc i8 %8 to i1, !dbg !220
  br i1 %9, label %bb6, label %bb5, !dbg !220

bb5:                                              ; preds = %bb6, %bb4
  %10 = load i8*, i8** %1, align 8, !dbg !221
  ret i8* %10, !dbg !221

bb6:                                              ; preds = %bb4
  br label %bb5, !dbg !220
}

define void @"_ZN50_$LT$T$u20$as$u20$core..convert..From$LT$T$GT$$GT$4from17h7fa262259b54d400E"() unnamed_addr #1 !dbg !222 {
start:
  ret void, !dbg !226
}

define nonnull i8* @"_ZN50_$LT$T$u20$as$u20$core..convert..Into$LT$U$GT$$GT$4into17h229fc97fdcaf9cb0E"(i8* nonnull %self) unnamed_addr #1 !dbg !227 {
start:
  %0 = call nonnull i8* @"_ZN119_$LT$core..ptr..non_null..NonNull$LT$T$GT$$u20$as$u20$core..convert..From$LT$core..ptr..unique..Unique$LT$T$GT$$GT$$GT$4from17hd2aa0243ea29611eE"(i8* nonnull %self), !dbg !229
  br label %bb1, !dbg !229

bb1:                                              ; preds = %start
  ret i8* %0, !dbg !230
}

define void @"_ZN53_$LT$T$u20$as$u20$alloc..alloc..WriteCloneIntoRaw$GT$20write_clone_into_raw17h92efcf7c5fbd8a00E"(i64** align 8 dereferenceable(8) %self, i64** %target) unnamed_addr #0 !dbg !231 {
start:
  %_5 = call noalias align 8 i64* @"_ZN51_$LT$example..Nat$u20$as$u20$core..clone..Clone$GT$5clone17hc1da32aed59b143dE"(i64** align 8 dereferenceable(8) %self), !dbg !236
  br label %bb1, !dbg !236

bb1:                                              ; preds = %start
  call void @llvm.experimental.noalias.scope.decl(metadata !237), !dbg !240
  call void @_ZN4core3ptr5write17h72a939caa164f97bE(i64** %target, i64* noalias align 8 %_5), !dbg !241
  br label %bb2, !dbg !240

bb2:                                              ; preds = %bb1
  ret void, !dbg !244
}

define internal void @"_ZN59_$LT$alloc..alloc..Global$u20$as$u20$core..clone..Clone$GT$5clone17hb266baec4793d7e5E"(%"alloc::alloc::Global"* nonnull align 1 %self) unnamed_addr #0 !dbg !245 {
start:
  ret void, !dbg !247
}

define internal i8* @_ZN5alloc5alloc12alloc_zeroed17h3d9aeda4548e17acE(i64 %0, i64 %1) unnamed_addr #0 !dbg !248 {
start:
  %layout = alloca { i64, i64 }, align 8
  %2 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %layout, i32 0, i32 0
  store i64 %0, i64* %2, align 8
  %3 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %layout, i32 0, i32 1
  store i64 %1, i64* %3, align 8
  %_2 = call i64 @_ZN4core5alloc6layout6Layout4size17h1aa94a8afe68f159E({ i64, i64 }* align 8 dereferenceable(16) %layout), !dbg !249
  br label %bb1, !dbg !249

bb1:                                              ; preds = %start
  %_4 = call i64 @_ZN4core5alloc6layout6Layout5align17hda36d11e4adac4adE({ i64, i64 }* align 8 dereferenceable(16) %layout), !dbg !250
  br label %bb2, !dbg !250

bb2:                                              ; preds = %bb1
  %4 = call i8* @__rust_alloc_zeroed(i64 %_2, i64 %_4) #7, !dbg !251
  br label %bb3, !dbg !251

bb3:                                              ; preds = %bb2
  ret i8* %4, !dbg !252
}

define internal i8* @_ZN5alloc5alloc15exchange_malloc17h93ab00f861f87e18E(i64 %size, i64 %align) unnamed_addr #0 !dbg !253 {
start:
  %_6 = alloca { i8*, i64 }, align 8
  %0 = call { i64, i64 } @_ZN4core5alloc6layout6Layout25from_size_align_unchecked17h864fda2504d46fd7E(i64 %size, i64 %align), !dbg !254
  %layout.0 = extractvalue { i64, i64 } %0, 0, !dbg !254
  %layout.1 = extractvalue { i64, i64 } %0, 1, !dbg !254
  br label %bb1, !dbg !254

bb1:                                              ; preds = %start
  %1 = call { i8*, i64 } @"_ZN63_$LT$alloc..alloc..Global$u20$as$u20$core..alloc..Allocator$GT$8allocate17h100700a97803899bE"(%"alloc::alloc::Global"* nonnull align 1 bitcast (<{ [0 x i8] }>* @alloc9 to %"alloc::alloc::Global"*), i64 %layout.0, i64 %layout.1), !dbg !255
  store { i8*, i64 } %1, { i8*, i64 }* %_6, align 8, !dbg !255
  br label %bb2, !dbg !255

bb2:                                              ; preds = %bb1
  %2 = bitcast { i8*, i64 }* %_6 to {}**, !dbg !255
  %3 = load {}*, {}** %2, align 8, !dbg !255
  %4 = icmp eq {}* %3, null, !dbg !255
  %_9 = select i1 %4, i64 1, i64 0, !dbg !255
  switch i64 %_9, label %bb4 [
    i64 0, label %bb5
    i64 1, label %bb3
  ], !dbg !256

bb4:                                              ; preds = %bb2
  unreachable, !dbg !255

bb5:                                              ; preds = %bb2
  %5 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %_6, i32 0, i32 0, !dbg !257
  %ptr.0 = load i8*, i8** %5, align 8, !dbg !257, !nonnull !5
  %6 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %_6, i32 0, i32 1, !dbg !257
  %ptr.1 = load i64, i64* %6, align 8, !dbg !257
  %7 = call i8* @"_ZN4core3ptr8non_null26NonNull$LT$$u5b$T$u5d$$GT$10as_mut_ptr17h86097296280f5b0dE"(i8* nonnull %ptr.0, i64 %ptr.1), !dbg !258
  br label %bb6, !dbg !258

bb3:                                              ; preds = %bb2
  call void @_ZN5alloc5alloc18handle_alloc_error17he21d1668e088475cE(i64 %layout.0, i64 %layout.1) #8, !dbg !259
  unreachable, !dbg !259

bb6:                                              ; preds = %bb5
  ret i8* %7, !dbg !260
}

define internal i8* @_ZN5alloc5alloc5alloc17h75b829b9b966de8dE(i64 %0, i64 %1) unnamed_addr #0 !dbg !261 {
start:
  %layout = alloca { i64, i64 }, align 8
  %2 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %layout, i32 0, i32 0
  store i64 %0, i64* %2, align 8
  %3 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %layout, i32 0, i32 1
  store i64 %1, i64* %3, align 8
  %_2 = call i64 @_ZN4core5alloc6layout6Layout4size17h1aa94a8afe68f159E({ i64, i64 }* align 8 dereferenceable(16) %layout), !dbg !262
  br label %bb1, !dbg !262

bb1:                                              ; preds = %start
  %_4 = call i64 @_ZN4core5alloc6layout6Layout5align17hda36d11e4adac4adE({ i64, i64 }* align 8 dereferenceable(16) %layout), !dbg !263
  br label %bb2, !dbg !263

bb2:                                              ; preds = %bb1
  %4 = call i8* @__rust_alloc(i64 %_2, i64 %_4) #7, !dbg !264
  br label %bb3, !dbg !264

bb3:                                              ; preds = %bb2
  ret i8* %4, !dbg !265
}

define internal { i8*, i64 } @_ZN5alloc5alloc6Global10alloc_impl17h3dce0da0d6380498E(%"alloc::alloc::Global"* nonnull align 1 %self, i64 %0, i64 %1, i1 zeroext %zeroed) unnamed_addr #0 !dbg !266 {
start:
  %_15 = alloca i8*, align 8
  %raw_ptr = alloca i8*, align 8
  %2 = alloca { i8*, i64 }, align 8
  %layout = alloca { i64, i64 }, align 8
  %3 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %layout, i32 0, i32 0
  store i64 %0, i64* %3, align 8
  %4 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %layout, i32 0, i32 1
  store i64 %1, i64* %4, align 8
  %_4 = call i64 @_ZN4core5alloc6layout6Layout4size17h1aa94a8afe68f159E({ i64, i64 }* align 8 dereferenceable(16) %layout), !dbg !268
  br label %bb1, !dbg !268

bb1:                                              ; preds = %start
  %5 = icmp eq i64 %_4, 0, !dbg !269
  br i1 %5, label %bb3, label %bb2, !dbg !269

bb3:                                              ; preds = %bb1
  %_7 = call nonnull i8* @_ZN4core5alloc6layout6Layout8dangling17h5e2014c69dca2d07E({ i64, i64 }* align 8 dereferenceable(16) %layout), !dbg !270
  br label %bb4, !dbg !270

bb2:                                              ; preds = %bb1
  br i1 %zeroed, label %bb6, label %bb8, !dbg !271

bb8:                                              ; preds = %bb2
  %6 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %layout, i32 0, i32 0, !dbg !272
  %_13.0 = load i64, i64* %6, align 8, !dbg !272
  %7 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %layout, i32 0, i32 1, !dbg !272
  %_13.1 = load i64, i64* %7, align 8, !dbg !272, !range !34
  %8 = call i8* @_ZN5alloc5alloc5alloc17h75b829b9b966de8dE(i64 %_13.0, i64 %_13.1), !dbg !273
  store i8* %8, i8** %raw_ptr, align 8, !dbg !273
  br label %bb9, !dbg !273

bb6:                                              ; preds = %bb2
  %9 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %layout, i32 0, i32 0, !dbg !274
  %_12.0 = load i64, i64* %9, align 8, !dbg !274
  %10 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %layout, i32 0, i32 1, !dbg !274
  %_12.1 = load i64, i64* %10, align 8, !dbg !274, !range !34
  %11 = call i8* @_ZN5alloc5alloc12alloc_zeroed17h3d9aeda4548e17acE(i64 %_12.0, i64 %_12.1), !dbg !275
  store i8* %11, i8** %raw_ptr, align 8, !dbg !275
  br label %bb7, !dbg !275

bb7:                                              ; preds = %bb6
  br label %bb10, !dbg !276

bb10:                                             ; preds = %bb9, %bb7
  %_18 = load i8*, i8** %raw_ptr, align 8, !dbg !277
  %_17 = call i8* @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$3new17hebae0b2290bdef64E"(i8* %_18), !dbg !278
  br label %bb11, !dbg !278

bb9:                                              ; preds = %bb8
  br label %bb10, !dbg !276

bb11:                                             ; preds = %bb10
  %_16 = call i8* @"_ZN4core6option15Option$LT$T$GT$5ok_or17h864498eacc8aacb9E"(i8* %_17), !dbg !278
  br label %bb12, !dbg !278

bb12:                                             ; preds = %bb11
  %12 = call i8* @"_ZN79_$LT$core..result..Result$LT$T$C$E$GT$$u20$as$u20$core..ops..try_trait..Try$GT$6branch17hfa197df2779087e9E"(i8* %_16), !dbg !278
  store i8* %12, i8** %_15, align 8, !dbg !278
  br label %bb13, !dbg !278

bb13:                                             ; preds = %bb12
  %13 = bitcast i8** %_15 to {}**, !dbg !278
  %14 = load {}*, {}** %13, align 8, !dbg !278
  %15 = icmp eq {}* %14, null, !dbg !278
  %_20 = select i1 %15, i64 1, i64 0, !dbg !278
  switch i64 %_20, label %bb15 [
    i64 0, label %bb14
    i64 1, label %bb16
  ], !dbg !278

bb15:                                             ; preds = %bb13
  unreachable, !dbg !278

bb14:                                             ; preds = %bb13
  %val = load i8*, i8** %_15, align 8, !dbg !278, !nonnull !5
  %16 = call { i8*, i64 } @"_ZN4core3ptr8non_null26NonNull$LT$$u5b$T$u5d$$GT$20slice_from_raw_parts17hbd76d94f6ce21ba6E"(i8* nonnull %val, i64 %_4), !dbg !279
  %_24.0 = extractvalue { i8*, i64 } %16, 0, !dbg !279
  %_24.1 = extractvalue { i8*, i64 } %16, 1, !dbg !279
  br label %bb18, !dbg !279

bb16:                                             ; preds = %bb13
  %17 = call { i8*, i64 } @"_ZN153_$LT$core..result..Result$LT$T$C$F$GT$$u20$as$u20$core..ops..try_trait..FromResidual$LT$core..result..Result$LT$core..convert..Infallible$C$E$GT$$GT$$GT$13from_residual17h3ebb6d63a873d87dE"(), !dbg !278
  store { i8*, i64 } %17, { i8*, i64 }* %2, align 8, !dbg !278
  br label %bb17, !dbg !278

bb17:                                             ; preds = %bb16
  br label %bb20, !dbg !280

bb20:                                             ; preds = %bb19, %bb17
  %18 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %2, i32 0, i32 0, !dbg !280
  %19 = load i8*, i8** %18, align 8, !dbg !280
  %20 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %2, i32 0, i32 1, !dbg !280
  %21 = load i64, i64* %20, align 8, !dbg !280
  %22 = insertvalue { i8*, i64 } undef, i8* %19, 0, !dbg !280
  %23 = insertvalue { i8*, i64 } %22, i64 %21, 1, !dbg !280
  ret { i8*, i64 } %23, !dbg !280

bb18:                                             ; preds = %bb14
  %24 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %2, i32 0, i32 0, !dbg !281
  store i8* %_24.0, i8** %24, align 8, !dbg !281
  %25 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %2, i32 0, i32 1, !dbg !281
  store i64 %_24.1, i64* %25, align 8, !dbg !281
  br label %bb19, !dbg !282

bb19:                                             ; preds = %bb5, %bb18
  br label %bb20, !dbg !280

bb4:                                              ; preds = %bb3
  %26 = call { i8*, i64 } @"_ZN4core3ptr8non_null26NonNull$LT$$u5b$T$u5d$$GT$20slice_from_raw_parts17hbd76d94f6ce21ba6E"(i8* nonnull %_7, i64 0), !dbg !283
  %_6.0 = extractvalue { i8*, i64 } %26, 0, !dbg !283
  %_6.1 = extractvalue { i8*, i64 } %26, 1, !dbg !283
  br label %bb5, !dbg !283

bb5:                                              ; preds = %bb4
  %27 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %2, i32 0, i32 0, !dbg !284
  store i8* %_6.0, i8** %27, align 8, !dbg !284
  %28 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %2, i32 0, i32 1, !dbg !284
  store i64 %_6.1, i64* %28, align 8, !dbg !284
  br label %bb19, !dbg !285
}

define internal void @_ZN5alloc5alloc7dealloc17h2b7d78147443628fE(i8* %ptr, i64 %0, i64 %1) unnamed_addr #0 !dbg !286 {
start:
  %layout = alloca { i64, i64 }, align 8
  %2 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %layout, i32 0, i32 0
  store i64 %0, i64* %2, align 8
  %3 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %layout, i32 0, i32 1
  store i64 %1, i64* %3, align 8
  %_4 = call i64 @_ZN4core5alloc6layout6Layout4size17h1aa94a8afe68f159E({ i64, i64 }* align 8 dereferenceable(16) %layout), !dbg !287
  br label %bb1, !dbg !287

bb1:                                              ; preds = %start
  %_6 = call i64 @_ZN4core5alloc6layout6Layout5align17hda36d11e4adac4adE({ i64, i64 }* align 8 dereferenceable(16) %layout), !dbg !288
  br label %bb2, !dbg !288

bb2:                                              ; preds = %bb1
  call void @__rust_dealloc(i8* %ptr, i64 %_4, i64 %_6) #7, !dbg !289
  br label %bb3, !dbg !289

bb3:                                              ; preds = %bb2
  ret void, !dbg !290
}

define void @_ZN5alloc5alloc8box_free17h487859dd7008df07E(i64* nonnull %0) unnamed_addr #0 personality i32 (i32, i32, i64, %"unwind::libunwind::_Unwind_Exception"*, %"unwind::libunwind::_Unwind_Context"*)* @rust_eh_personality !dbg !291 {
start:
  %1 = alloca i64, align 8
  %2 = alloca i64, align 8
  %3 = alloca { i8*, i32 }, align 8
  %alloc = alloca %"alloc::alloc::Global", align 1
  %ptr = alloca i64*, align 8
  store i64* %0, i64** %ptr, align 8
  %_5 = invoke align 8 dereferenceable(24) %"Vector<Nat>"* @"_ZN4core3ptr6unique15Unique$LT$T$GT$6as_ref17he5982509a295a41bE"(i64** align 8 dereferenceable(8) %ptr)
          to label %bb1 unwind label %cleanup, !dbg !292

bb1:                                              ; preds = %start
  store i64 24, i64* %2, align 8, !dbg !293
  %size = load i64, i64* %2, align 8, !dbg !293
  br label %bb2, !dbg !293

bb10:                                             ; preds = %cleanup
  br label %bb11, !dbg !294

cleanup:                                          ; preds = %bb7, %bb6, %bb5, %bb4, %bb2, %start
  %4 = landingpad { i8*, i32 }
          cleanup
  %5 = extractvalue { i8*, i32 } %4, 0
  %6 = extractvalue { i8*, i32 } %4, 1
  %7 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %3, i32 0, i32 0
  store i8* %5, i8** %7, align 8
  %8 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %3, i32 0, i32 1
  store i32 %6, i32* %8, align 8
  br label %bb10

bb2:                                              ; preds = %bb1
  %_9 = invoke align 8 dereferenceable(24) %"Vector<Nat>"* @"_ZN4core3ptr6unique15Unique$LT$T$GT$6as_ref17he5982509a295a41bE"(i64** align 8 dereferenceable(8) %ptr)
          to label %bb3 unwind label %cleanup, !dbg !295

bb3:                                              ; preds = %bb2
  store i64 8, i64* %1, align 8, !dbg !296
  %align = load i64, i64* %1, align 8, !dbg !296
  br label %bb4, !dbg !296

bb4:                                              ; preds = %bb3
  %9 = invoke { i64, i64 } @_ZN4core5alloc6layout6Layout25from_size_align_unchecked17h864fda2504d46fd7E(i64 %size, i64 %align)
          to label %bb5 unwind label %cleanup, !dbg !297

bb5:                                              ; preds = %bb4
  %layout.0 = extractvalue { i64, i64 } %9, 0, !dbg !297
  %layout.1 = extractvalue { i64, i64 } %9, 1, !dbg !297
  %_17 = load i64*, i64** %ptr, align 8, !dbg !298, !nonnull !5
  %_16 = invoke nonnull i8* @"_ZN4core3ptr6unique15Unique$LT$T$GT$4cast17h1f55cacfc2510c05E"(i64* nonnull %_17)
          to label %bb6 unwind label %cleanup, !dbg !298

bb6:                                              ; preds = %bb5
  %_15 = invoke nonnull i8* @"_ZN50_$LT$T$u20$as$u20$core..convert..Into$LT$U$GT$$GT$4into17h229fc97fdcaf9cb0E"(i8* nonnull %_16)
          to label %bb7 unwind label %cleanup, !dbg !298

bb7:                                              ; preds = %bb6
  invoke void @"_ZN63_$LT$alloc..alloc..Global$u20$as$u20$core..alloc..Allocator$GT$10deallocate17hd3bd3ec965c53a9aE"(%"alloc::alloc::Global"* nonnull align 1 %alloc, i8* nonnull %_15, i64 %layout.0, i64 %layout.1)
          to label %bb8 unwind label %cleanup, !dbg !299

bb8:                                              ; preds = %bb7
  br label %bb9, !dbg !294

bb11:                                             ; preds = %bb10
  %10 = bitcast { i8*, i32 }* %3 to i8**, !dbg !300
  %11 = load i8*, i8** %10, align 8, !dbg !300
  %12 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %3, i32 0, i32 1, !dbg !300
  %13 = load i32, i32* %12, align 8, !dbg !300
  %14 = insertvalue { i8*, i32 } undef, i8* %11, 0, !dbg !300
  %15 = insertvalue { i8*, i32 } %14, i32 %13, 1, !dbg !300
  resume { i8*, i32 } %15, !dbg !300

bb9:                                              ; preds = %bb8
  ret void, !dbg !301
}

define void @_ZN5alloc5alloc8box_free17h4df5a02897cf5996E(i64* nonnull %0) unnamed_addr #0 personality i32 (i32, i32, i64, %"unwind::libunwind::_Unwind_Exception"*, %"unwind::libunwind::_Unwind_Context"*)* @rust_eh_personality !dbg !302 {
start:
  %1 = alloca i64, align 8
  %2 = alloca i64, align 8
  %3 = alloca { i8*, i32 }, align 8
  %alloc = alloca %"alloc::alloc::Global", align 1
  %ptr = alloca i64*, align 8
  store i64* %0, i64** %ptr, align 8
  %_5 = invoke align 8 dereferenceable(8) i8** @"_ZN4core3ptr6unique15Unique$LT$T$GT$6as_ref17h6a184e1ed3728056E"(i64** align 8 dereferenceable(8) %ptr)
          to label %bb1 unwind label %cleanup, !dbg !303

bb1:                                              ; preds = %start
  store i64 8, i64* %2, align 8, !dbg !304
  %size = load i64, i64* %2, align 8, !dbg !304
  br label %bb2, !dbg !304

bb10:                                             ; preds = %cleanup
  br label %bb11, !dbg !305

cleanup:                                          ; preds = %bb7, %bb6, %bb5, %bb4, %bb2, %start
  %4 = landingpad { i8*, i32 }
          cleanup
  %5 = extractvalue { i8*, i32 } %4, 0
  %6 = extractvalue { i8*, i32 } %4, 1
  %7 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %3, i32 0, i32 0
  store i8* %5, i8** %7, align 8
  %8 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %3, i32 0, i32 1
  store i32 %6, i32* %8, align 8
  br label %bb10

bb2:                                              ; preds = %bb1
  %_9 = invoke align 8 dereferenceable(8) i8** @"_ZN4core3ptr6unique15Unique$LT$T$GT$6as_ref17h6a184e1ed3728056E"(i64** align 8 dereferenceable(8) %ptr)
          to label %bb3 unwind label %cleanup, !dbg !306

bb3:                                              ; preds = %bb2
  store i64 8, i64* %1, align 8, !dbg !307
  %align = load i64, i64* %1, align 8, !dbg !307
  br label %bb4, !dbg !307

bb4:                                              ; preds = %bb3
  %9 = invoke { i64, i64 } @_ZN4core5alloc6layout6Layout25from_size_align_unchecked17h864fda2504d46fd7E(i64 %size, i64 %align)
          to label %bb5 unwind label %cleanup, !dbg !308

bb5:                                              ; preds = %bb4
  %layout.0 = extractvalue { i64, i64 } %9, 0, !dbg !308
  %layout.1 = extractvalue { i64, i64 } %9, 1, !dbg !308
  %_17 = load i64*, i64** %ptr, align 8, !dbg !309, !nonnull !5
  %_16 = invoke nonnull i8* @"_ZN4core3ptr6unique15Unique$LT$T$GT$4cast17hf9fab5d337fb7077E"(i64* nonnull %_17)
          to label %bb6 unwind label %cleanup, !dbg !309

bb6:                                              ; preds = %bb5
  %_15 = invoke nonnull i8* @"_ZN50_$LT$T$u20$as$u20$core..convert..Into$LT$U$GT$$GT$4into17h229fc97fdcaf9cb0E"(i8* nonnull %_16)
          to label %bb7 unwind label %cleanup, !dbg !309

bb7:                                              ; preds = %bb6
  invoke void @"_ZN63_$LT$alloc..alloc..Global$u20$as$u20$core..alloc..Allocator$GT$10deallocate17hd3bd3ec965c53a9aE"(%"alloc::alloc::Global"* nonnull align 1 %alloc, i8* nonnull %_15, i64 %layout.0, i64 %layout.1)
          to label %bb8 unwind label %cleanup, !dbg !310

bb8:                                              ; preds = %bb7
  br label %bb9, !dbg !305

bb11:                                             ; preds = %bb10
  %10 = bitcast { i8*, i32 }* %3 to i8**, !dbg !311
  %11 = load i8*, i8** %10, align 8, !dbg !311
  %12 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %3, i32 0, i32 1, !dbg !311
  %13 = load i32, i32* %12, align 8, !dbg !311
  %14 = insertvalue { i8*, i32 } undef, i8* %11, 0, !dbg !311
  %15 = insertvalue { i8*, i32 } %14, i32 %13, 1, !dbg !311
  resume { i8*, i32 } %15, !dbg !311

bb9:                                              ; preds = %bb8
  ret void, !dbg !312
}

define void @_ZN5alloc5alloc8box_free17h75d3a0df5b182abcE(i64* nonnull %0) unnamed_addr #0 personality i32 (i32, i32, i64, %"unwind::libunwind::_Unwind_Exception"*, %"unwind::libunwind::_Unwind_Context"*)* @rust_eh_personality !dbg !313 {
start:
  %1 = alloca i64, align 8
  %2 = alloca i64, align 8
  %3 = alloca { i8*, i32 }, align 8
  %alloc = alloca %"alloc::alloc::Global", align 1
  %ptr = alloca i64*, align 8
  store i64* %0, i64** %ptr, align 8
  %_5 = invoke align 8 dereferenceable(8) i64** @"_ZN4core3ptr6unique15Unique$LT$T$GT$6as_ref17h8acdb05c0d378c35E"(i64** align 8 dereferenceable(8) %ptr)
          to label %bb1 unwind label %cleanup, !dbg !314

bb1:                                              ; preds = %start
  store i64 8, i64* %2, align 8, !dbg !315
  %size = load i64, i64* %2, align 8, !dbg !315
  br label %bb2, !dbg !315

bb10:                                             ; preds = %cleanup
  br label %bb11, !dbg !316

cleanup:                                          ; preds = %bb7, %bb6, %bb5, %bb4, %bb2, %start
  %4 = landingpad { i8*, i32 }
          cleanup
  %5 = extractvalue { i8*, i32 } %4, 0
  %6 = extractvalue { i8*, i32 } %4, 1
  %7 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %3, i32 0, i32 0
  store i8* %5, i8** %7, align 8
  %8 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %3, i32 0, i32 1
  store i32 %6, i32* %8, align 8
  br label %bb10

bb2:                                              ; preds = %bb1
  %_9 = invoke align 8 dereferenceable(8) i64** @"_ZN4core3ptr6unique15Unique$LT$T$GT$6as_ref17h8acdb05c0d378c35E"(i64** align 8 dereferenceable(8) %ptr)
          to label %bb3 unwind label %cleanup, !dbg !317

bb3:                                              ; preds = %bb2
  store i64 8, i64* %1, align 8, !dbg !318
  %align = load i64, i64* %1, align 8, !dbg !318
  br label %bb4, !dbg !318

bb4:                                              ; preds = %bb3
  %9 = invoke { i64, i64 } @_ZN4core5alloc6layout6Layout25from_size_align_unchecked17h864fda2504d46fd7E(i64 %size, i64 %align)
          to label %bb5 unwind label %cleanup, !dbg !319

bb5:                                              ; preds = %bb4
  %layout.0 = extractvalue { i64, i64 } %9, 0, !dbg !319
  %layout.1 = extractvalue { i64, i64 } %9, 1, !dbg !319
  %_17 = load i64*, i64** %ptr, align 8, !dbg !320, !nonnull !5
  %_16 = invoke nonnull i8* @"_ZN4core3ptr6unique15Unique$LT$T$GT$4cast17h8efa5f9215b55e0cE"(i64* nonnull %_17)
          to label %bb6 unwind label %cleanup, !dbg !320

bb6:                                              ; preds = %bb5
  %_15 = invoke nonnull i8* @"_ZN50_$LT$T$u20$as$u20$core..convert..Into$LT$U$GT$$GT$4into17h229fc97fdcaf9cb0E"(i8* nonnull %_16)
          to label %bb7 unwind label %cleanup, !dbg !320

bb7:                                              ; preds = %bb6
  invoke void @"_ZN63_$LT$alloc..alloc..Global$u20$as$u20$core..alloc..Allocator$GT$10deallocate17hd3bd3ec965c53a9aE"(%"alloc::alloc::Global"* nonnull align 1 %alloc, i8* nonnull %_15, i64 %layout.0, i64 %layout.1)
          to label %bb8 unwind label %cleanup, !dbg !321

bb8:                                              ; preds = %bb7
  br label %bb9, !dbg !316

bb11:                                             ; preds = %bb10
  %10 = bitcast { i8*, i32 }* %3 to i8**, !dbg !322
  %11 = load i8*, i8** %10, align 8, !dbg !322
  %12 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %3, i32 0, i32 1, !dbg !322
  %13 = load i32, i32* %12, align 8, !dbg !322
  %14 = insertvalue { i8*, i32 } undef, i8* %11, 0, !dbg !322
  %15 = insertvalue { i8*, i32 } %14, i32 %13, 1, !dbg !322
  resume { i8*, i32 } %15, !dbg !322

bb9:                                              ; preds = %bb8
  ret void, !dbg !323
}

define noalias nonnull align 8 i64** @"_ZN5alloc5boxed16Box$LT$T$C$A$GT$11from_raw_in17hf8b7f11e56727d61E"(i64** %raw) unnamed_addr #0 personality i32 (i32, i32, i64, %"unwind::libunwind::_Unwind_Exception"*, %"unwind::libunwind::_Unwind_Context"*)* @rust_eh_personality !dbg !324 {
start:
  %0 = alloca { i8*, i32 }, align 8
  %1 = alloca i64**, align 8
  %_3 = invoke nonnull i64* @"_ZN4core3ptr6unique15Unique$LT$T$GT$13new_unchecked17h52e4cab5bec4cf56E"(i64** %raw)
          to label %bb1 unwind label %cleanup, !dbg !328

bb1:                                              ; preds = %start
  %2 = bitcast i64*** %1 to i64**, !dbg !329
  store i64* %_3, i64** %2, align 8, !dbg !329
  %3 = bitcast i64*** %1 to %"alloc::alloc::Global"*, !dbg !329
  %4 = load i64**, i64*** %1, align 8, !dbg !330, !nonnull !5
  ret i64** %4, !dbg !330

bb2:                                              ; preds = %cleanup
  br label %bb3, !dbg !331

cleanup:                                          ; preds = %start
  %5 = landingpad { i8*, i32 }
          cleanup
  %6 = extractvalue { i8*, i32 } %5, 0
  %7 = extractvalue { i8*, i32 } %5, 1
  %8 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 0
  store i8* %6, i8** %8, align 8
  %9 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1
  store i32 %7, i32* %9, align 8
  br label %bb2

bb3:                                              ; preds = %bb2
  %10 = bitcast { i8*, i32 }* %0 to i8**, !dbg !332
  %11 = load i8*, i8** %10, align 8, !dbg !332
  %12 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1, !dbg !332
  %13 = load i32, i32* %12, align 8, !dbg !332
  %14 = insertvalue { i8*, i32 } undef, i8* %11, 0, !dbg !332
  %15 = insertvalue { i8*, i32 } %14, i32 %13, 1, !dbg !332
  resume { i8*, i32 } %15, !dbg !332
}

define noalias nonnull align 8 i8** @"_ZN5alloc5boxed16Box$LT$T$C$A$GT$11from_raw_in17hf96095d2e51f7b21E"(i8** %raw) unnamed_addr #0 personality i32 (i32, i32, i64, %"unwind::libunwind::_Unwind_Exception"*, %"unwind::libunwind::_Unwind_Context"*)* @rust_eh_personality !dbg !333 {
start:
  %0 = alloca { i8*, i32 }, align 8
  %1 = alloca i8**, align 8
  %_3 = invoke nonnull i64* @"_ZN4core3ptr6unique15Unique$LT$T$GT$13new_unchecked17hf5d39441e41f2a4fE"(i8** %raw)
          to label %bb1 unwind label %cleanup, !dbg !334

bb1:                                              ; preds = %start
  %2 = bitcast i8*** %1 to i64**, !dbg !335
  store i64* %_3, i64** %2, align 8, !dbg !335
  %3 = bitcast i8*** %1 to %"alloc::alloc::Global"*, !dbg !335
  %4 = load i8**, i8*** %1, align 8, !dbg !336, !nonnull !5
  ret i8** %4, !dbg !336

bb2:                                              ; preds = %cleanup
  br label %bb3, !dbg !337

cleanup:                                          ; preds = %start
  %5 = landingpad { i8*, i32 }
          cleanup
  %6 = extractvalue { i8*, i32 } %5, 0
  %7 = extractvalue { i8*, i32 } %5, 1
  %8 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 0
  store i8* %6, i8** %8, align 8
  %9 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1
  store i32 %7, i32* %9, align 8
  br label %bb2

bb3:                                              ; preds = %bb2
  %10 = bitcast { i8*, i32 }* %0 to i8**, !dbg !338
  %11 = load i8*, i8** %10, align 8, !dbg !338
  %12 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1, !dbg !338
  %13 = load i32, i32* %12, align 8, !dbg !338
  %14 = insertvalue { i8*, i32 } undef, i8* %11, 0, !dbg !338
  %15 = insertvalue { i8*, i32 } %14, i32 %13, 1, !dbg !338
  resume { i8*, i32 } %15, !dbg !338
}

define nonnull i64* @"_ZN5alloc5boxed16Box$LT$T$C$A$GT$11into_unique17h9240de697d627c8aE"(i8** noalias nonnull align 8 %0) unnamed_addr #0 personality i32 (i32, i32, i64, %"unwind::libunwind::_Unwind_Exception"*, %"unwind::libunwind::_Unwind_Context"*)* @rust_eh_personality !dbg !339 {
start:
  %1 = alloca { i8*, i32 }, align 8
  %_9 = alloca i8, align 1
  %2 = alloca i64*, align 8
  %b = alloca i8**, align 8
  store i8** %0, i8*** %b, align 8
  store i8 0, i8* %_9, align 1, !dbg !340
  store i8 1, i8* %_9, align 1, !dbg !340
  %_4 = bitcast i8*** %b to %"alloc::alloc::Global"*, !dbg !341
  invoke void @_ZN4core3ptr4read17h8d527a36feb68ea4E(%"alloc::alloc::Global"* %_4)
          to label %bb1 unwind label %cleanup, !dbg !342

bb1:                                              ; preds = %start
  store i8 0, i8* %_9, align 1, !dbg !343
  %_7 = load i8**, i8*** %b, align 8, !dbg !343, !nonnull !5
  %_6 = invoke align 8 dereferenceable(8) i8** @"_ZN5alloc5boxed16Box$LT$T$C$A$GT$4leak17he30850f21833189cE"(i8** noalias nonnull align 8 %_7)
          to label %bb2 unwind label %cleanup1, !dbg !344

bb7:                                              ; preds = %bb4, %cleanup
  %3 = load i8, i8* %_9, align 1, !dbg !345, !range !121
  %4 = trunc i8 %3 to i1, !dbg !345
  br i1 %4, label %bb6, label %bb5, !dbg !345

cleanup:                                          ; preds = %start
  %5 = landingpad { i8*, i32 }
          cleanup
  %6 = extractvalue { i8*, i32 } %5, 0
  %7 = extractvalue { i8*, i32 } %5, 1
  %8 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %1, i32 0, i32 0
  store i8* %6, i8** %8, align 8
  %9 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %1, i32 0, i32 1
  store i32 %7, i32* %9, align 8
  br label %bb7

bb2:                                              ; preds = %bb1
  %_5 = invoke nonnull i64* @"_ZN95_$LT$core..ptr..unique..Unique$LT$T$GT$$u20$as$u20$core..convert..From$LT$$RF$mut$u20$T$GT$$GT$4from17hde5f97e3edc375efE"(i8** align 8 dereferenceable(8) %_6)
          to label %bb3 unwind label %cleanup1, !dbg !346

bb4:                                              ; preds = %cleanup1
  br label %bb7, !dbg !345

cleanup1:                                         ; preds = %bb2, %bb1
  %10 = landingpad { i8*, i32 }
          cleanup
  %11 = extractvalue { i8*, i32 } %10, 0
  %12 = extractvalue { i8*, i32 } %10, 1
  %13 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %1, i32 0, i32 0
  store i8* %11, i8** %13, align 8
  %14 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %1, i32 0, i32 1
  store i32 %12, i32* %14, align 8
  br label %bb4

bb3:                                              ; preds = %bb2
  store i64* %_5, i64** %2, align 8, !dbg !347
  %15 = bitcast i64** %2 to i8*, !dbg !347
  %16 = getelementptr i8, i8* %15, i64 8, !dbg !347
  %17 = bitcast i8* %16 to %"alloc::alloc::Global"*, !dbg !347
  %18 = load i64*, i64** %2, align 8, !dbg !348, !nonnull !5
  ret i64* %18, !dbg !348

bb5:                                              ; preds = %bb6, %bb7
  %19 = bitcast { i8*, i32 }* %1 to i8**, !dbg !349
  %20 = load i8*, i8** %19, align 8, !dbg !349
  %21 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %1, i32 0, i32 1, !dbg !349
  %22 = load i32, i32* %21, align 8, !dbg !349
  %23 = insertvalue { i8*, i32 } undef, i8* %20, 0, !dbg !349
  %24 = insertvalue { i8*, i32 } %23, i32 %22, 1, !dbg !349
  resume { i8*, i32 } %24, !dbg !349

bb6:                                              ; preds = %bb7
  call void @"_ZN4core3ptr102drop_in_place$LT$alloc..boxed..Box$LT$core..mem..maybe_uninit..MaybeUninit$LT$example..Nat$GT$$GT$$GT$17h0268a0cddce88eceE"(i8*** %b) #6, !dbg !345
  br label %bb5, !dbg !345
}

define noalias nonnull align 8 i8** @"_ZN5alloc5boxed16Box$LT$T$C$A$GT$13new_uninit_in17h9777df8051afc524E"() unnamed_addr #1 personality i32 (i32, i32, i64, %"unwind::libunwind::_Unwind_Exception"*, %"unwind::libunwind::_Unwind_Context"*)* @rust_eh_personality !dbg !350 {
start:
  %0 = alloca { i8*, i32 }, align 8
  %_7 = alloca i8, align 1
  %_3 = alloca i64*, align 8
  store i8 0, i8* %_7, align 1, !dbg !352
  store i8 1, i8* %_7, align 1, !dbg !352
  %1 = invoke { i64, i64 } @_ZN4core5alloc6layout6Layout3new17hbb5ff3defbc8cbc0E()
          to label %bb1 unwind label %cleanup, !dbg !353

bb1:                                              ; preds = %start
  %layout.0 = extractvalue { i64, i64 } %1, 0, !dbg !353
  %layout.1 = extractvalue { i64, i64 } %1, 1, !dbg !353
  store i8 0, i8* %_7, align 1, !dbg !354
  %2 = invoke noalias align 8 i64* @"_ZN5alloc5boxed16Box$LT$T$C$A$GT$17try_new_uninit_in17h87455bd4f6b0d803E"()
          to label %bb2 unwind label %cleanup, !dbg !355

bb8:                                              ; preds = %cleanup
  %3 = load i8, i8* %_7, align 1, !dbg !356, !range !121
  %4 = trunc i8 %3 to i1, !dbg !356
  br i1 %4, label %bb7, label %bb6, !dbg !356

cleanup:                                          ; preds = %bb1, %start
  %5 = landingpad { i8*, i32 }
          cleanup
  %6 = extractvalue { i8*, i32 } %5, 0
  %7 = extractvalue { i8*, i32 } %5, 1
  %8 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 0
  store i8* %6, i8** %8, align 8
  %9 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1
  store i32 %7, i32* %9, align 8
  br label %bb8

bb2:                                              ; preds = %bb1
  store i64* %2, i64** %_3, align 8, !dbg !355
  %10 = bitcast i64** %_3 to {}**, !dbg !355
  %11 = load {}*, {}** %10, align 8, !dbg !355
  %12 = icmp eq {}* %11, null, !dbg !355
  %_5 = select i1 %12, i64 1, i64 0, !dbg !355
  switch i64 %_5, label %bb4 [
    i64 0, label %bb5
    i64 1, label %bb3
  ], !dbg !357

bb6:                                              ; preds = %bb7, %bb8
  %13 = bitcast { i8*, i32 }* %0 to i8**, !dbg !358
  %14 = load i8*, i8** %13, align 8, !dbg !358
  %15 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1, !dbg !358
  %16 = load i32, i32* %15, align 8, !dbg !358
  %17 = insertvalue { i8*, i32 } undef, i8* %14, 0, !dbg !358
  %18 = insertvalue { i8*, i32 } %17, i32 %16, 1, !dbg !358
  resume { i8*, i32 } %18, !dbg !358

bb7:                                              ; preds = %bb8
  br label %bb6, !dbg !356

bb4:                                              ; preds = %bb2
  unreachable, !dbg !355

bb5:                                              ; preds = %bb2
  %19 = bitcast i64** %_3 to i8***, !dbg !359
  %m = load i8**, i8*** %19, align 8, !dbg !359, !nonnull !5
  ret i8** %m, !dbg !360

bb3:                                              ; preds = %bb2
  call void @_ZN5alloc5alloc18handle_alloc_error17he21d1668e088475cE(i64 %layout.0, i64 %layout.1) #8, !dbg !361
  unreachable, !dbg !361
}

define noalias align 8 i64* @"_ZN5alloc5boxed16Box$LT$T$C$A$GT$17try_new_uninit_in17h87455bd4f6b0d803E"() unnamed_addr #1 personality i32 (i32, i32, i64, %"unwind::libunwind::_Unwind_Exception"*, %"unwind::libunwind::_Unwind_Context"*)* @rust_eh_personality !dbg !362 {
start:
  %0 = alloca { i8*, i32 }, align 8
  %_17 = alloca i8, align 1
  %_5 = alloca { i8*, i64 }, align 8
  %1 = alloca i64*, align 8
  %alloc = alloca %"alloc::alloc::Global", align 1
  store i8 0, i8* %_17, align 1, !dbg !363
  store i8 1, i8* %_17, align 1, !dbg !363
  %2 = invoke { i64, i64 } @_ZN4core5alloc6layout6Layout3new17hbb5ff3defbc8cbc0E()
          to label %bb1 unwind label %cleanup, !dbg !364

bb1:                                              ; preds = %start
  %layout.0 = extractvalue { i64, i64 } %2, 0, !dbg !364
  %layout.1 = extractvalue { i64, i64 } %2, 1, !dbg !364
  %3 = invoke { i8*, i64 } @"_ZN63_$LT$alloc..alloc..Global$u20$as$u20$core..alloc..Allocator$GT$8allocate17h100700a97803899bE"(%"alloc::alloc::Global"* nonnull align 1 %alloc, i64 %layout.0, i64 %layout.1)
          to label %bb2 unwind label %cleanup, !dbg !365

bb14:                                             ; preds = %cleanup
  %4 = load i8, i8* %_17, align 1, !dbg !366, !range !121
  %5 = trunc i8 %4 to i1, !dbg !366
  br i1 %5, label %bb13, label %bb12, !dbg !366

cleanup:                                          ; preds = %bb9, %bb8, %bb4, %bb6, %bb2, %bb1, %start
  %6 = landingpad { i8*, i32 }
          cleanup
  %7 = extractvalue { i8*, i32 } %6, 0
  %8 = extractvalue { i8*, i32 } %6, 1
  %9 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 0
  store i8* %7, i8** %9, align 8
  %10 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1
  store i32 %8, i32* %10, align 8
  br label %bb14

bb2:                                              ; preds = %bb1
  %_6.0 = extractvalue { i8*, i64 } %3, 0, !dbg !365
  %_6.1 = extractvalue { i8*, i64 } %3, 1, !dbg !365
  %11 = invoke { i8*, i64 } @"_ZN79_$LT$core..result..Result$LT$T$C$E$GT$$u20$as$u20$core..ops..try_trait..Try$GT$6branch17haec1218b4b12ac36E"(i8* %_6.0, i64 %_6.1)
          to label %bb3 unwind label %cleanup, !dbg !365

bb3:                                              ; preds = %bb2
  store { i8*, i64 } %11, { i8*, i64 }* %_5, align 8, !dbg !365
  %12 = bitcast { i8*, i64 }* %_5 to {}**, !dbg !365
  %13 = load {}*, {}** %12, align 8, !dbg !365
  %14 = icmp eq {}* %13, null, !dbg !365
  %_9 = select i1 %14, i64 1, i64 0, !dbg !365
  switch i64 %_9, label %bb5 [
    i64 0, label %bb4
    i64 1, label %bb6
  ], !dbg !365

bb5:                                              ; preds = %bb3
  unreachable, !dbg !365

bb4:                                              ; preds = %bb3
  %15 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %_5, i32 0, i32 0, !dbg !365
  %val.0 = load i8*, i8** %15, align 8, !dbg !365, !nonnull !5
  %16 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %_5, i32 0, i32 1, !dbg !365
  %val.1 = load i64, i64* %16, align 8, !dbg !365
  %ptr = invoke nonnull i64* @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$4cast17h052232ae0084c658E"(i8* nonnull %val.0, i64 %val.1)
          to label %bb8 unwind label %cleanup, !dbg !365

bb6:                                              ; preds = %bb3
  %17 = invoke noalias align 8 i64* @"_ZN153_$LT$core..result..Result$LT$T$C$F$GT$$u20$as$u20$core..ops..try_trait..FromResidual$LT$core..result..Result$LT$core..convert..Infallible$C$E$GT$$GT$$GT$13from_residual17hc93f3bf83ce972faE"()
          to label %bb7 unwind label %cleanup, !dbg !365

bb7:                                              ; preds = %bb6
  store i64* %17, i64** %1, align 8, !dbg !365
  br label %bb11, !dbg !366

bb11:                                             ; preds = %bb10, %bb7
  %18 = load i64*, i64** %1, align 8, !dbg !367
  ret i64* %18, !dbg !367

bb8:                                              ; preds = %bb4
  %_14 = invoke i8** @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$6as_ptr17h374e705f028538d8E"(i64* nonnull %ptr)
          to label %bb9 unwind label %cleanup, !dbg !368

bb9:                                              ; preds = %bb8
  store i8 0, i8* %_17, align 1, !dbg !369
  %_13 = invoke noalias nonnull align 8 i8** @"_ZN5alloc5boxed16Box$LT$T$C$A$GT$11from_raw_in17hf96095d2e51f7b21E"(i8** %_14)
          to label %bb10 unwind label %cleanup, !dbg !370

bb10:                                             ; preds = %bb9
  %19 = bitcast i64** %1 to i8***, !dbg !371
  store i8** %_13, i8*** %19, align 8, !dbg !371
  br label %bb11, !dbg !366

bb12:                                             ; preds = %bb13, %bb14
  %20 = bitcast { i8*, i32 }* %0 to i8**, !dbg !372
  %21 = load i8*, i8** %20, align 8, !dbg !372
  %22 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1, !dbg !372
  %23 = load i32, i32* %22, align 8, !dbg !372
  %24 = insertvalue { i8*, i32 } undef, i8* %21, 0, !dbg !372
  %25 = insertvalue { i8*, i32 } %24, i32 %23, 1, !dbg !372
  resume { i8*, i32 } %25, !dbg !372

bb13:                                             ; preds = %bb14
  br label %bb12, !dbg !366
}

define i64* @"_ZN5alloc5boxed16Box$LT$T$C$A$GT$23into_raw_with_allocator17haf5312fdc711ca6cE"(i8** noalias nonnull align 8 %b) unnamed_addr #0 personality i32 (i32, i32, i64, %"unwind::libunwind::_Unwind_Exception"*, %"unwind::libunwind::_Unwind_Context"*)* @rust_eh_personality !dbg !373 {
start:
  %0 = alloca { i8*, i32 }, align 8
  %1 = alloca i64*, align 8
  %_4 = call nonnull i64* @"_ZN5alloc5boxed16Box$LT$T$C$A$GT$11into_unique17h9240de697d627c8aE"(i8** noalias nonnull align 8 %b), !dbg !374
  br label %bb1, !dbg !374

bb1:                                              ; preds = %start
  %_6 = invoke i8** @"_ZN4core3ptr6unique15Unique$LT$T$GT$6as_ptr17h91f3760617147a77E"(i64* nonnull %_4)
          to label %bb2 unwind label %cleanup, !dbg !375

bb2:                                              ; preds = %bb1
  %2 = bitcast i64** %1 to i8***, !dbg !376
  store i8** %_6, i8*** %2, align 8, !dbg !376
  %3 = bitcast i64** %1 to i8*, !dbg !376
  %4 = getelementptr i8, i8* %3, i64 8, !dbg !376
  %5 = bitcast i8* %4 to %"alloc::alloc::Global"*, !dbg !376
  %6 = load i64*, i64** %1, align 8, !dbg !377
  ret i64* %6, !dbg !377

bb3:                                              ; preds = %cleanup
  br label %bb4, !dbg !378

cleanup:                                          ; preds = %bb1
  %7 = landingpad { i8*, i32 }
          cleanup
  %8 = extractvalue { i8*, i32 } %7, 0
  %9 = extractvalue { i8*, i32 } %7, 1
  %10 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 0
  store i8* %8, i8** %10, align 8
  %11 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1
  store i32 %9, i32* %11, align 8
  br label %bb3

bb4:                                              ; preds = %bb3
  %12 = bitcast { i8*, i32 }* %0 to i8**, !dbg !379
  %13 = load i8*, i8** %12, align 8, !dbg !379
  %14 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1, !dbg !379
  %15 = load i32, i32* %14, align 8, !dbg !379
  %16 = insertvalue { i8*, i32 } undef, i8* %13, 0, !dbg !379
  %17 = insertvalue { i8*, i32 } %16, i32 %15, 1, !dbg !379
  resume { i8*, i32 } %17, !dbg !379
}

define align 8 dereferenceable(8) i8** @"_ZN5alloc5boxed16Box$LT$T$C$A$GT$4leak17he30850f21833189cE"(i8** noalias nonnull align 8 %b) unnamed_addr #0 !dbg !380 {
start:
  %0 = alloca i64*, align 8
  %_9 = alloca i64*, align 8
  call void @llvm.experimental.noalias.scope.decl(metadata !381), !dbg !384
  %1 = bitcast i64** %0 to i8***, !dbg !385
  store i8** %b, i8*** %1, align 8, !dbg !385, !noalias !381
  %2 = load i64*, i64** %0, align 8, !dbg !391, !noalias !381, !nonnull !5
  store i64* %2, i64** %_9, align 8, !dbg !384
  br label %bb1, !dbg !384

bb1:                                              ; preds = %start
  %3 = bitcast i64** %_9 to i8***, !dbg !392
  br label %bb2, !dbg !384

bb2:                                              ; preds = %bb1
  %4 = bitcast i8*** %3 to i64**, !dbg !384
  %_6 = load i64*, i64** %4, align 8, !dbg !384, !nonnull !5
  %_5 = call i8** @"_ZN4core3ptr6unique15Unique$LT$T$GT$6as_ptr17h91f3760617147a77E"(i64* nonnull %_6), !dbg !384
  br label %bb3, !dbg !384

bb3:                                              ; preds = %bb2
  ret i8** %_5, !dbg !396
}

define noalias nonnull align 8 i64** @"_ZN5alloc5boxed60Box$LT$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$C$A$GT$11assume_init17h8cccd70791177617E"(i8** noalias nonnull align 8 %self) unnamed_addr #0 personality i32 (i32, i32, i64, %"unwind::libunwind::_Unwind_Exception"*, %"unwind::libunwind::_Unwind_Context"*)* @rust_eh_personality !dbg !397 {
start:
  %0 = alloca { i8*, i32 }, align 8
  %_9 = alloca i8, align 1
  store i8 0, i8* %_9, align 1, !dbg !399
  %_4 = call i64* @"_ZN5alloc5boxed16Box$LT$T$C$A$GT$23into_raw_with_allocator17haf5312fdc711ca6cE"(i8** noalias nonnull align 8 %self), !dbg !399
  br label %bb1, !dbg !399

bb1:                                              ; preds = %start
  %raw = bitcast i64* %_4 to i8**, !dbg !400
  store i8 1, i8* %_9, align 1, !dbg !401
  %_6 = bitcast i8** %raw to i64**, !dbg !402
  store i8 0, i8* %_9, align 1, !dbg !403
  %1 = invoke noalias nonnull align 8 i64** @"_ZN5alloc5boxed16Box$LT$T$C$A$GT$11from_raw_in17hf8b7f11e56727d61E"(i64** %_6)
          to label %bb2 unwind label %cleanup, !dbg !404

bb2:                                              ; preds = %bb1
  store i8 0, i8* %_9, align 1, !dbg !405
  ret i64** %1, !dbg !406

bb3:                                              ; preds = %cleanup
  %2 = load i8, i8* %_9, align 1, !dbg !405, !range !121
  %3 = trunc i8 %2 to i1, !dbg !405
  br i1 %3, label %bb5, label %bb4, !dbg !405

cleanup:                                          ; preds = %bb1
  %4 = landingpad { i8*, i32 }
          cleanup
  %5 = extractvalue { i8*, i32 } %4, 0
  %6 = extractvalue { i8*, i32 } %4, 1
  %7 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 0
  store i8* %5, i8** %7, align 8
  %8 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1
  store i32 %6, i32* %8, align 8
  br label %bb3

bb4:                                              ; preds = %bb5, %bb3
  %9 = bitcast { i8*, i32 }* %0 to i8**, !dbg !407
  %10 = load i8*, i8** %9, align 8, !dbg !407
  %11 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1, !dbg !407
  %12 = load i32, i32* %11, align 8, !dbg !407
  %13 = insertvalue { i8*, i32 } undef, i8* %10, 0, !dbg !407
  %14 = insertvalue { i8*, i32 } %13, i32 %12, 1, !dbg !407
  resume { i8*, i32 } %14, !dbg !407

bb5:                                              ; preds = %bb3
  br label %bb4, !dbg !405
}

define internal void @"_ZN63_$LT$alloc..alloc..Global$u20$as$u20$core..alloc..Allocator$GT$10deallocate17hd3bd3ec965c53a9aE"(%"alloc::alloc::Global"* nonnull align 1 %self, i8* nonnull %ptr, i64 %0, i64 %1) unnamed_addr #0 !dbg !408 {
start:
  %layout = alloca { i64, i64 }, align 8
  %2 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %layout, i32 0, i32 0
  store i64 %0, i64* %2, align 8
  %3 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %layout, i32 0, i32 1
  store i64 %1, i64* %3, align 8
  %_4 = call i64 @_ZN4core5alloc6layout6Layout4size17h1aa94a8afe68f159E({ i64, i64 }* align 8 dereferenceable(16) %layout), !dbg !410
  br label %bb1, !dbg !410

bb1:                                              ; preds = %start
  %4 = icmp eq i64 %_4, 0, !dbg !410
  br i1 %4, label %bb5, label %bb2, !dbg !410

bb5:                                              ; preds = %bb1
  br label %bb6, !dbg !411

bb2:                                              ; preds = %bb1
  %_6 = call i8* @"_ZN4core3ptr8non_null16NonNull$LT$T$GT$6as_ptr17h42c4b7e5250d107bE"(i8* nonnull %ptr), !dbg !412
  br label %bb3, !dbg !412

bb3:                                              ; preds = %bb2
  %5 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %layout, i32 0, i32 0, !dbg !413
  %_8.0 = load i64, i64* %5, align 8, !dbg !413
  %6 = getelementptr inbounds { i64, i64 }, { i64, i64 }* %layout, i32 0, i32 1, !dbg !413
  %_8.1 = load i64, i64* %6, align 8, !dbg !413, !range !34
  call void @_ZN5alloc5alloc7dealloc17h2b7d78147443628fE(i8* %_6, i64 %_8.0, i64 %_8.1), !dbg !414
  br label %bb4, !dbg !414

bb4:                                              ; preds = %bb3
  br label %bb6, !dbg !411

bb6:                                              ; preds = %bb5, %bb4
  ret void, !dbg !415
}

define internal { i8*, i64 } @"_ZN63_$LT$alloc..alloc..Global$u20$as$u20$core..alloc..Allocator$GT$8allocate17h100700a97803899bE"(%"alloc::alloc::Global"* nonnull align 1 %self, i64 %layout.0, i64 %layout.1) unnamed_addr #0 !dbg !416 {
start:
  %0 = call { i8*, i64 } @_ZN5alloc5alloc6Global10alloc_impl17h3dce0da0d6380498E(%"alloc::alloc::Global"* nonnull align 1 %self, i64 %layout.0, i64 %layout.1, i1 zeroext false), !dbg !417
  %1 = extractvalue { i8*, i64 } %0, 0, !dbg !417
  %2 = extractvalue { i8*, i64 } %0, 1, !dbg !417
  br label %bb1, !dbg !417

bb1:                                              ; preds = %start
  %3 = insertvalue { i8*, i64 } undef, i8* %1, 0, !dbg !418
  %4 = insertvalue { i8*, i64 } %3, i64 %2, 1, !dbg !418
  ret { i8*, i64 } %4, !dbg !418
}

define noalias nonnull align 8 i64** @"_ZN69_$LT$alloc..boxed..Box$LT$T$C$A$GT$$u20$as$u20$core..clone..Clone$GT$5clone17he460e5310f703f67E"(i64*** align 8 dereferenceable(8) %self) unnamed_addr #0 personality i32 (i32, i32, i64, %"unwind::libunwind::_Unwind_Exception"*, %"unwind::libunwind::_Unwind_Context"*)* @rust_eh_personality !dbg !419 {
start:
  %0 = alloca { i8*, i32 }, align 8
  %_10 = alloca i8, align 1
  %boxed = alloca i8**, align 8
  store i8 0, i8* %_10, align 1, !dbg !421
  %_4 = bitcast i64*** %self to %"alloc::alloc::Global"*, !dbg !422
  call void @"_ZN59_$LT$alloc..alloc..Global$u20$as$u20$core..clone..Clone$GT$5clone17hb266baec4793d7e5E"(%"alloc::alloc::Global"* nonnull align 1 %_4), !dbg !422
  br label %bb1, !dbg !422

bb1:                                              ; preds = %start
  %1 = call noalias nonnull align 8 i8** @"_ZN5alloc5boxed16Box$LT$T$C$A$GT$13new_uninit_in17h9777df8051afc524E"(), !dbg !423
  store i8** %1, i8*** %boxed, align 8, !dbg !423
  br label %bb2, !dbg !423

bb2:                                              ; preds = %bb1
  store i8 1, i8* %_10, align 1, !dbg !424
  %_6 = load i64**, i64*** %self, align 8, !dbg !425, !nonnull !5
  %_8 = load i8**, i8*** %boxed, align 8, !dbg !426, !nonnull !5
  %2 = bitcast i8** %_8 to i64**, !dbg !427
  br label %bb3, !dbg !430

bb3:                                              ; preds = %bb2
  invoke void @"_ZN53_$LT$T$u20$as$u20$alloc..alloc..WriteCloneIntoRaw$GT$20write_clone_into_raw17h92efcf7c5fbd8a00E"(i64** align 8 dereferenceable(8) %_6, i64** %2)
          to label %bb4 unwind label %cleanup, !dbg !425

bb8:                                              ; preds = %cleanup
  %3 = load i8, i8* %_10, align 1, !dbg !431, !range !121
  %4 = trunc i8 %3 to i1, !dbg !431
  br i1 %4, label %bb7, label %bb6, !dbg !431

cleanup:                                          ; preds = %bb4, %bb3
  %5 = landingpad { i8*, i32 }
          cleanup
  %6 = extractvalue { i8*, i32 } %5, 0
  %7 = extractvalue { i8*, i32 } %5, 1
  %8 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 0
  store i8* %6, i8** %8, align 8
  %9 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1
  store i32 %7, i32* %9, align 8
  br label %bb8

bb4:                                              ; preds = %bb3
  store i8 0, i8* %_10, align 1, !dbg !432
  %_9 = load i8**, i8*** %boxed, align 8, !dbg !432, !nonnull !5
  %10 = invoke noalias nonnull align 8 i64** @"_ZN5alloc5boxed60Box$LT$core..mem..maybe_uninit..MaybeUninit$LT$T$GT$$C$A$GT$11assume_init17h8cccd70791177617E"(i8** noalias nonnull align 8 %_9)
          to label %bb5 unwind label %cleanup, !dbg !432

bb5:                                              ; preds = %bb4
  store i8 0, i8* %_10, align 1, !dbg !431
  ret i64** %10, !dbg !433

bb6:                                              ; preds = %bb7, %bb8
  %11 = bitcast { i8*, i32 }* %0 to i8**, !dbg !434
  %12 = load i8*, i8** %11, align 8, !dbg !434
  %13 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1, !dbg !434
  %14 = load i32, i32* %13, align 8, !dbg !434
  %15 = insertvalue { i8*, i32 } undef, i8* %12, 0, !dbg !434
  %16 = insertvalue { i8*, i32 } %15, i32 %14, 1, !dbg !434
  resume { i8*, i32 } %16, !dbg !434

bb7:                                              ; preds = %bb8
  call void @"_ZN4core3ptr102drop_in_place$LT$alloc..boxed..Box$LT$core..mem..maybe_uninit..MaybeUninit$LT$example..Nat$GT$$GT$$GT$17h0268a0cddce88eceE"(i8*** %boxed) #6, !dbg !431
  br label %bb6, !dbg !431
}

define { i8*, i64 } @"_ZN79_$LT$core..result..Result$LT$T$C$E$GT$$u20$as$u20$core..ops..try_trait..Try$GT$6branch17haec1218b4b12ac36E"(i8* %0, i64 %1) unnamed_addr #0 !dbg !435 {
start:
  %_6 = alloca %"core::result::Result<core::convert::Infallible, core::alloc::AllocError>::Err", align 1
  %2 = alloca { i8*, i64 }, align 8
  %self = alloca { i8*, i64 }, align 8
  %3 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %self, i32 0, i32 0
  store i8* %0, i8** %3, align 8
  %4 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %self, i32 0, i32 1
  store i64 %1, i64* %4, align 8
  %5 = bitcast { i8*, i64 }* %self to {}**, !dbg !437
  %6 = load {}*, {}** %5, align 8, !dbg !437
  %7 = icmp eq {}* %6, null, !dbg !437
  %_2 = select i1 %7, i64 1, i64 0, !dbg !437
  switch i64 %_2, label %bb2 [
    i64 0, label %bb3
    i64 1, label %bb1
  ], !dbg !438

bb2:                                              ; preds = %start
  unreachable, !dbg !437

bb3:                                              ; preds = %start
  %8 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %self, i32 0, i32 0, !dbg !439
  %v.0 = load i8*, i8** %8, align 8, !dbg !439, !nonnull !5
  %9 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %self, i32 0, i32 1, !dbg !439
  %v.1 = load i64, i64* %9, align 8, !dbg !439
  %10 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %2, i32 0, i32 0, !dbg !440
  store i8* %v.0, i8** %10, align 8, !dbg !440
  %11 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %2, i32 0, i32 1, !dbg !440
  store i64 %v.1, i64* %11, align 8, !dbg !440
  br label %bb4, !dbg !441

bb1:                                              ; preds = %start
  %12 = bitcast %"core::result::Result<core::convert::Infallible, core::alloc::AllocError>::Err"* %_6 to %"core::alloc::AllocError"*, !dbg !442
  %13 = bitcast { i8*, i64 }* %2 to %"core::ops::control_flow::ControlFlow<core::result::Result<core::convert::Infallible, core::alloc::AllocError>, core::ptr::non_null::NonNull<[u8]>>::Break"*, !dbg !443
  %14 = bitcast %"core::ops::control_flow::ControlFlow<core::result::Result<core::convert::Infallible, core::alloc::AllocError>, core::ptr::non_null::NonNull<[u8]>>::Break"* %13 to %"core::result::Result<core::convert::Infallible, core::alloc::AllocError>::Err"*, !dbg !443
  %15 = bitcast { i8*, i64 }* %2 to {}**, !dbg !443
  store {}* null, {}** %15, align 8, !dbg !443
  br label %bb4, !dbg !444

bb4:                                              ; preds = %bb3, %bb1
  %16 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %2, i32 0, i32 0, !dbg !445
  %17 = load i8*, i8** %16, align 8, !dbg !445
  %18 = getelementptr inbounds { i8*, i64 }, { i8*, i64 }* %2, i32 0, i32 1, !dbg !445
  %19 = load i64, i64* %18, align 8, !dbg !445
  %20 = insertvalue { i8*, i64 } undef, i8* %17, 0, !dbg !445
  %21 = insertvalue { i8*, i64 } %20, i64 %19, 1, !dbg !445
  ret { i8*, i64 } %21, !dbg !445
}

define i8* @"_ZN79_$LT$core..result..Result$LT$T$C$E$GT$$u20$as$u20$core..ops..try_trait..Try$GT$6branch17hfa197df2779087e9E"(i8* %0) unnamed_addr #0 !dbg !446 {
start:
  %_6 = alloca %"core::result::Result<core::convert::Infallible, core::alloc::AllocError>::Err", align 1
  %1 = alloca i8*, align 8
  %self = alloca i8*, align 8
  store i8* %0, i8** %self, align 8
  %2 = bitcast i8** %self to {}**, !dbg !447
  %3 = load {}*, {}** %2, align 8, !dbg !447
  %4 = icmp eq {}* %3, null, !dbg !447
  %_2 = select i1 %4, i64 1, i64 0, !dbg !447
  switch i64 %_2, label %bb2 [
    i64 0, label %bb3
    i64 1, label %bb1
  ], !dbg !448

bb2:                                              ; preds = %start
  unreachable, !dbg !447

bb3:                                              ; preds = %start
  %v = load i8*, i8** %self, align 8, !dbg !449, !nonnull !5
  store i8* %v, i8** %1, align 8, !dbg !450
  br label %bb4, !dbg !451

bb1:                                              ; preds = %start
  %5 = bitcast %"core::result::Result<core::convert::Infallible, core::alloc::AllocError>::Err"* %_6 to %"core::alloc::AllocError"*, !dbg !452
  %6 = bitcast i8** %1 to %"core::ops::control_flow::ControlFlow<core::result::Result<core::convert::Infallible, core::alloc::AllocError>, core::ptr::non_null::NonNull<u8>>::Break"*, !dbg !453
  %7 = bitcast %"core::ops::control_flow::ControlFlow<core::result::Result<core::convert::Infallible, core::alloc::AllocError>, core::ptr::non_null::NonNull<u8>>::Break"* %6 to %"core::result::Result<core::convert::Infallible, core::alloc::AllocError>::Err"*, !dbg !453
  %8 = bitcast i8** %1 to {}**, !dbg !453
  store {}* null, {}** %8, align 8, !dbg !453
  br label %bb4, !dbg !454

bb4:                                              ; preds = %bb3, %bb1
  %9 = load i8*, i8** %1, align 8, !dbg !455
  ret i8* %9, !dbg !455
}

define nonnull i64* @"_ZN95_$LT$core..ptr..unique..Unique$LT$T$GT$$u20$as$u20$core..convert..From$LT$$RF$mut$u20$T$GT$$GT$4from17hde5f97e3edc375efE"(i8** align 8 dereferenceable(8) %reference) unnamed_addr #0 !dbg !456 {
start:
  %0 = alloca i64*, align 8
  %1 = bitcast i64** %0 to i8***, !dbg !458
  store i8** %reference, i8*** %1, align 8, !dbg !458
  %2 = load i64*, i64** %0, align 8, !dbg !459, !nonnull !5
  ret i64* %2, !dbg !459
}

define internal noalias align 8 i64* @_ZN7example3add17h9537c70f390d829dE(i64* noalias align 8 %0, i64* noalias align 8 %m) unnamed_addr #1 personality i32 (i32, i32, i64, %"unwind::libunwind::_Unwind_Exception"*, %"unwind::libunwind::_Unwind_Context"*)* @rust_eh_personality !dbg !460 {
start:
  %1 = alloca { i8*, i32 }, align 8
  %x.i = alloca i64*, align 8
  %2 = alloca { i8*, i32 }, align 8
  %3 = alloca i64*, align 8
  %n = alloca i64*, align 8
  store i64* %0, i64** %n, align 8
  %4 = bitcast i64** %n to {}**, !dbg !463
  %5 = load {}*, {}** %4, align 8, !dbg !463
  %6 = icmp eq {}* %5, null, !dbg !463
  %_3 = select i1 %6, i64 0, i64 1, !dbg !463
  switch i64 %_3, label %bb2 [
    i64 0, label %bb3
    i64 1, label %bb1
  ], !dbg !464

bb2:                                              ; preds = %start
  unreachable, !dbg !463

bb3:                                              ; preds = %start
  store i64* %m, i64** %3, align 8, !dbg !465
  br label %bb6, !dbg !465

bb1:                                              ; preds = %start
  %7 = bitcast i64** %n to i64***, !dbg !466
  %p = load i64**, i64*** %7, align 8, !dbg !466, !nonnull !5
  %_7 = load i64*, i64** %p, align 8, !dbg !467
  %_6 = invoke noalias align 8 i64* @_ZN7example3add17h9537c70f390d829dE(i64* noalias align 8 %_7, i64* noalias align 8 %m)
          to label %bb4 unwind label %cleanup, !dbg !468

bb4:                                              ; preds = %bb1
  call void @llvm.experimental.noalias.scope.decl(metadata !469), !dbg !472
  store i64* %_6, i64** %x.i, align 8, !noalias !469
  %_4.i = invoke i8* @_ZN5alloc5alloc15exchange_malloc17h93ab00f861f87e18E(i64 8, i64 8)
          to label %"_ZN5alloc5boxed12Box$LT$T$GT$3new17h5da07b2339095e49E.exit" unwind label %cleanup.i, !dbg !473

cleanup.i:                                        ; preds = %bb4
  %8 = landingpad { i8*, i32 }
          cleanup
  %9 = extractvalue { i8*, i32 } %8, 0
  %10 = extractvalue { i8*, i32 } %8, 1
  %11 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %1, i32 0, i32 0
  store i8* %9, i8** %11, align 8, !noalias !469
  %12 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %1, i32 0, i32 1
  store i32 %10, i32* %12, align 8, !noalias !469
  invoke void @"_ZN4core3ptr33drop_in_place$LT$example..Nat$GT$17h4500bbe220c40510E"(i64** %x.i) #6
          to label %.noexc unwind label %cleanup, !dbg !477

.noexc:                                           ; preds = %cleanup.i
  %13 = bitcast { i8*, i32 }* %1 to i8**, !dbg !478
  %14 = load i8*, i8** %13, align 8, !dbg !478, !noalias !469
  %15 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %1, i32 0, i32 1, !dbg !478
  %16 = load i32, i32* %15, align 8, !dbg !478, !noalias !469
  %17 = insertvalue { i8*, i32 } undef, i8* %14, 0, !dbg !478
  %18 = insertvalue { i8*, i32 } %17, i32 %16, 1, !dbg !478
  br label %cleanup.body

"_ZN5alloc5boxed12Box$LT$T$GT$3new17h5da07b2339095e49E.exit": ; preds = %bb4
  %19 = bitcast i8* %_4.i to i64**, !dbg !473
  %20 = load i64*, i64** %x.i, align 8, !dbg !479, !noalias !469
  store i64* %20, i64** %19, align 8, !dbg !479
  br label %bb5, !dbg !480

bb7:                                              ; preds = %cleanup.body
  %21 = bitcast i64** %p to i64*, !dbg !481
  call void @_ZN5alloc5alloc8box_free17h75d3a0df5b182abcE(i64* nonnull %21) #6, !dbg !481
  br label %bb8, !dbg !481

cleanup:                                          ; preds = %cleanup.i, %bb1
  %22 = landingpad { i8*, i32 }
          cleanup
  br label %cleanup.body

cleanup.body:                                     ; preds = %.noexc, %cleanup
  %eh.lpad-body = phi { i8*, i32 } [ %22, %cleanup ], [ %18, %.noexc ]
  %23 = extractvalue { i8*, i32 } %eh.lpad-body, 0
  %24 = extractvalue { i8*, i32 } %eh.lpad-body, 1
  %25 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %2, i32 0, i32 0
  store i8* %23, i8** %25, align 8
  %26 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %2, i32 0, i32 1
  store i32 %24, i32* %26, align 8
  br label %bb7

bb5:                                              ; preds = %"_ZN5alloc5boxed12Box$LT$T$GT$3new17h5da07b2339095e49E.exit"
  %27 = bitcast i64** %3 to i64***, !dbg !482
  store i64** %19, i64*** %27, align 8, !dbg !482
  %28 = bitcast i64** %p to i64*, !dbg !481
  call void @_ZN5alloc5alloc8box_free17h75d3a0df5b182abcE(i64* nonnull %28), !dbg !481
  br label %bb6, !dbg !481

bb8:                                              ; preds = %bb7
  %29 = bitcast { i8*, i32 }* %2 to i8**, !dbg !483
  %30 = load i8*, i8** %29, align 8, !dbg !483
  %31 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %2, i32 0, i32 1, !dbg !483
  %32 = load i32, i32* %31, align 8, !dbg !483
  %33 = insertvalue { i8*, i32 } undef, i8* %30, 0, !dbg !483
  %34 = insertvalue { i8*, i32 } %33, i32 %32, 1, !dbg !483
  resume { i8*, i32 } %34, !dbg !483

bb6:                                              ; preds = %bb3, %bb5
  %35 = load i64*, i64** %3, align 8, !dbg !484
  ret i64* %35, !dbg !484
}

define internal noalias align 8 i64* @_ZN7example7one_nat17h807de8f0aa557d66E() unnamed_addr #1 personality i32 (i32, i32, i64, %"unwind::libunwind::_Unwind_Exception"*, %"unwind::libunwind::_Unwind_Context"*)* @rust_eh_personality !dbg !485 {
start:
  %0 = alloca { i8*, i32 }, align 8
  %x.i = alloca i64*, align 8
  %_2 = alloca i64*, align 8
  %1 = alloca i64*, align 8
  %2 = bitcast i64** %_2 to {}**, !dbg !486
  store {}* null, {}** %2, align 8, !dbg !486
  %3 = load i64*, i64** %_2, align 8, !dbg !487
  call void @llvm.experimental.noalias.scope.decl(metadata !488), !dbg !487
  store i64* %3, i64** %x.i, align 8, !noalias !488
  %_4.i = invoke i8* @_ZN5alloc5alloc15exchange_malloc17h93ab00f861f87e18E(i64 8, i64 8)
          to label %"_ZN5alloc5boxed12Box$LT$T$GT$3new17h5da07b2339095e49E.exit" unwind label %cleanup.i, !dbg !491

cleanup.i:                                        ; preds = %start
  %4 = landingpad { i8*, i32 }
          cleanup
  %5 = extractvalue { i8*, i32 } %4, 0
  %6 = extractvalue { i8*, i32 } %4, 1
  %7 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 0
  store i8* %5, i8** %7, align 8, !noalias !488
  %8 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1
  store i32 %6, i32* %8, align 8, !noalias !488
  call void @"_ZN4core3ptr33drop_in_place$LT$example..Nat$GT$17h4500bbe220c40510E"(i64** %x.i) #6, !dbg !493
  %9 = bitcast { i8*, i32 }* %0 to i8**, !dbg !494
  %10 = load i8*, i8** %9, align 8, !dbg !494, !noalias !488
  %11 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1, !dbg !494
  %12 = load i32, i32* %11, align 8, !dbg !494, !noalias !488
  %13 = insertvalue { i8*, i32 } undef, i8* %10, 0, !dbg !494
  %14 = insertvalue { i8*, i32 } %13, i32 %12, 1, !dbg !494
  resume { i8*, i32 } %14, !dbg !494

"_ZN5alloc5boxed12Box$LT$T$GT$3new17h5da07b2339095e49E.exit": ; preds = %start
  %15 = bitcast i8* %_4.i to i64**, !dbg !491
  %16 = load i64*, i64** %x.i, align 8, !dbg !495, !noalias !488
  store i64* %16, i64** %15, align 8, !dbg !495
  br label %bb1, !dbg !487

bb1:                                              ; preds = %"_ZN5alloc5boxed12Box$LT$T$GT$3new17h5da07b2339095e49E.exit"
  %17 = bitcast i64** %1 to i64***, !dbg !496
  store i64** %15, i64*** %17, align 8, !dbg !496
  %18 = load i64*, i64** %1, align 8, !dbg !497
  ret i64* %18, !dbg !497
}

define internal void @_ZN7example6append17hc9590437c6280dd9E(%"Vector<Nat>"* noalias nocapture sret(%"Vector<Nat>") dereferenceable(24) %0, i64* noalias align 8 %1, i64* noalias align 8 %2, %"Vector<Nat>"* noalias nocapture dereferenceable(24) %v, %"Vector<Nat>"* noalias nocapture dereferenceable(24) %w) unnamed_addr #1 personality i32 (i32, i32, i64, %"unwind::libunwind::_Unwind_Exception"*, %"unwind::libunwind::_Unwind_Context"*)* @rust_eh_personality !dbg !498 {
start:
  %3 = alloca { i8*, i32 }, align 8
  %4 = alloca { i8*, i32 }, align 8
  %_25 = alloca i8, align 1
  %_24 = alloca i8, align 1
  %_23 = alloca i8, align 1
  %_22 = alloca i8, align 1
  %_21 = alloca i8, align 1
  %_20 = alloca %"Vector<Nat>", align 8
  %_19 = alloca %"Vector<Nat>", align 8
  %_16 = alloca %"Vector<Nat>", align 8
  %_11 = alloca i64*, align 8
  %_10 = alloca i64*, align 8
  %_9 = alloca i64*, align 8
  %n0 = alloca i64*, align 8
  %p = alloca i64*, align 8
  %_1 = alloca i64*, align 8
  store i64* %1, i64** %_1, align 8
  store i64* %2, i64** %p, align 8
  store i8 0, i8* %_21, align 1, !dbg !499
  store i8 0, i8* %_24, align 1, !dbg !499
  store i8 0, i8* %_25, align 1, !dbg !499
  store i8 0, i8* %_23, align 1, !dbg !499
  store i8 0, i8* %_22, align 1, !dbg !499
  store i8 1, i8* %_21, align 1, !dbg !499
  store i8 1, i8* %_25, align 1, !dbg !499
  %5 = getelementptr inbounds %"Vector<Nat>", %"Vector<Nat>"* %v, i32 0, i32 1, !dbg !499
  %6 = load {}*, {}** %5, align 8, !dbg !499
  %7 = icmp eq {}* %6, null, !dbg !499
  %_5 = select i1 %7, i64 0, i64 1, !dbg !499
  switch i64 %_5, label %bb2 [
    i64 0, label %bb3
    i64 1, label %bb1
  ], !dbg !500

bb2:                                              ; preds = %start
  unreachable, !dbg !499

bb3:                                              ; preds = %start
  store i8 0, i8* %_25, align 1, !dbg !501
  %8 = bitcast %"Vector<Nat>"* %0 to i8*, !dbg !501
  %9 = bitcast %"Vector<Nat>"* %w to i8*, !dbg !501
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %8, i8* align 8 %9, i64 24, i1 false), !dbg !501
  br label %bb19, !dbg !501

bb1:                                              ; preds = %start
  %10 = bitcast %"Vector<Nat>"* %v to %"Vector<Nat>::Cons"*, !dbg !502
  %11 = bitcast %"Vector<Nat>::Cons"* %10 to i64**, !dbg !502
  %a = load i64*, i64** %11, align 8, !dbg !502
  store i8 1, i8* %_24, align 1, !dbg !503
  %12 = bitcast %"Vector<Nat>"* %v to %"Vector<Nat>::Cons"*, !dbg !503
  %13 = getelementptr inbounds %"Vector<Nat>::Cons", %"Vector<Nat>::Cons"* %12, i32 0, i32 1, !dbg !503
  %14 = load i64*, i64** %13, align 8, !dbg !503
  store i64* %14, i64** %n0, align 8, !dbg !503
  store i8 1, i8* %_23, align 1, !dbg !504
  %15 = bitcast %"Vector<Nat>"* %v to %"Vector<Nat>::Cons"*, !dbg !504
  %16 = getelementptr inbounds %"Vector<Nat>::Cons", %"Vector<Nat>::Cons"* %15, i32 0, i32 2, !dbg !504
  %vector = load %"Vector<Nat>"*, %"Vector<Nat>"** %16, align 8, !dbg !504, !nonnull !5
  store i64* %a, i64** %_9, align 8, !dbg !505
  %17 = invoke noalias align 8 i64* @"_ZN51_$LT$example..Nat$u20$as$u20$core..clone..Clone$GT$5clone17hc1da32aed59b143dE"(i64** align 8 dereferenceable(8) %n0)
          to label %bb4 unwind label %cleanup, !dbg !506

bb4:                                              ; preds = %bb1
  store i64* %17, i64** %_11, align 8, !dbg !506
  store i8 1, i8* %_22, align 1, !dbg !507
  %_13 = invoke noalias align 8 i64* @"_ZN51_$LT$example..Nat$u20$as$u20$core..clone..Clone$GT$5clone17hc1da32aed59b143dE"(i64** align 8 dereferenceable(8) %p)
          to label %bb5 unwind label %cleanup1, !dbg !508

bb13:                                             ; preds = %bb12, %bb21, %bb22, %cleanup
  call void @"_ZN4core3ptr33drop_in_place$LT$example..Nat$GT$17h4500bbe220c40510E"(i64** %_9) #6, !dbg !509
  br label %bb25, !dbg !509

cleanup:                                          ; preds = %bb1
  %18 = landingpad { i8*, i32 }
          cleanup
  %19 = extractvalue { i8*, i32 } %18, 0
  %20 = extractvalue { i8*, i32 } %18, 1
  %21 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %4, i32 0, i32 0
  store i8* %19, i8** %21, align 8
  %22 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %4, i32 0, i32 1
  store i32 %20, i32* %22, align 8
  br label %bb13

bb5:                                              ; preds = %bb4
  store i8 0, i8* %_22, align 1, !dbg !510
  %23 = load i64*, i64** %_11, align 8, !dbg !510
  %24 = invoke noalias align 8 i64* @_ZN7example3add17h9537c70f390d829dE(i64* noalias align 8 %23, i64* noalias align 8 %_13)
          to label %bb6 unwind label %cleanup1, !dbg !510

bb22:                                             ; preds = %cleanup1
  %25 = load i8, i8* %_22, align 1, !dbg !511, !range !121
  %26 = trunc i8 %25 to i1, !dbg !511
  br i1 %26, label %bb21, label %bb13, !dbg !511

cleanup1:                                         ; preds = %bb5, %bb4
  %27 = landingpad { i8*, i32 }
          cleanup
  %28 = extractvalue { i8*, i32 } %27, 0
  %29 = extractvalue { i8*, i32 } %27, 1
  %30 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %4, i32 0, i32 0
  store i8* %28, i8** %30, align 8
  %31 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %4, i32 0, i32 1
  store i32 %29, i32* %31, align 8
  br label %bb22

bb6:                                              ; preds = %bb5
  store i64* %24, i64** %_10, align 8, !dbg !510
  store i8 0, i8* %_22, align 1, !dbg !511
  store i8 0, i8* %_24, align 1, !dbg !512
  %_17 = load i64*, i64** %n0, align 8, !dbg !512
  store i8 0, i8* %_21, align 1, !dbg !513
  %_18 = load i64*, i64** %p, align 8, !dbg !513
  store i8 0, i8* %_23, align 1, !dbg !514
  %32 = bitcast %"Vector<Nat>"* %_19 to i8*, !dbg !514
  %33 = bitcast %"Vector<Nat>"* %vector to i8*, !dbg !514
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %32, i8* align 8 %33, i64 24, i1 false), !dbg !514
  store i8 0, i8* %_25, align 1, !dbg !515
  %34 = bitcast %"Vector<Nat>"* %_20 to i8*, !dbg !515
  %35 = bitcast %"Vector<Nat>"* %w to i8*, !dbg !515
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %34, i8* align 8 %35, i64 24, i1 false), !dbg !515
  invoke void @_ZN7example6append17hc9590437c6280dd9E(%"Vector<Nat>"* noalias nocapture sret(%"Vector<Nat>") dereferenceable(24) %_16, i64* noalias align 8 %_17, i64* noalias align 8 %_18, %"Vector<Nat>"* noalias nocapture dereferenceable(24) %_19, %"Vector<Nat>"* noalias nocapture dereferenceable(24) %_20)
          to label %bb7 unwind label %cleanup2, !dbg !516

bb21:                                             ; preds = %bb22
  call void @"_ZN4core3ptr33drop_in_place$LT$example..Nat$GT$17h4500bbe220c40510E"(i64** %_11) #6, !dbg !511
  br label %bb13, !dbg !511

bb7:                                              ; preds = %bb6
  call void @llvm.experimental.noalias.scope.decl(metadata !517), !dbg !520
  %_4.i = invoke i8* @_ZN5alloc5alloc15exchange_malloc17h93ab00f861f87e18E(i64 24, i64 8)
          to label %"_ZN5alloc5boxed12Box$LT$T$GT$3new17h486da4461c2b397bE.exit" unwind label %cleanup.i, !dbg !521, !noalias !517

cleanup.i:                                        ; preds = %bb7
  %36 = landingpad { i8*, i32 }
          cleanup
  %37 = extractvalue { i8*, i32 } %36, 0
  %38 = extractvalue { i8*, i32 } %36, 1
  %39 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %3, i32 0, i32 0
  store i8* %37, i8** %39, align 8, !noalias !517
  %40 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %3, i32 0, i32 1
  store i32 %38, i32* %40, align 8, !noalias !517
  invoke void @"_ZN4core3ptr56drop_in_place$LT$example..Vector$LT$example..Nat$GT$$GT$17h86962fbc7676f71eE"(%"Vector<Nat>"* %_16) #6
          to label %.noexc unwind label %cleanup2, !dbg !524

.noexc:                                           ; preds = %cleanup.i
  %41 = bitcast { i8*, i32 }* %3 to i8**, !dbg !525
  %42 = load i8*, i8** %41, align 8, !dbg !525, !noalias !517
  %43 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %3, i32 0, i32 1, !dbg !525
  %44 = load i32, i32* %43, align 8, !dbg !525, !noalias !517
  %45 = insertvalue { i8*, i32 } undef, i8* %42, 0, !dbg !525
  %46 = insertvalue { i8*, i32 } %45, i32 %44, 1, !dbg !525
  br label %cleanup2.body

"_ZN5alloc5boxed12Box$LT$T$GT$3new17h486da4461c2b397bE.exit": ; preds = %bb7
  %47 = bitcast i8* %_4.i to %"Vector<Nat>"*, !dbg !521
  %48 = bitcast %"Vector<Nat>"* %_16 to i8*, !dbg !526
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %_4.i, i8* align 8 %48, i64 24, i1 false), !dbg !526
  br label %bb8, !dbg !527

bb12:                                             ; preds = %cleanup2.body
  call void @"_ZN4core3ptr33drop_in_place$LT$example..Nat$GT$17h4500bbe220c40510E"(i64** %_10) #6, !dbg !509
  br label %bb13, !dbg !509

cleanup2:                                         ; preds = %cleanup.i, %bb6
  %49 = landingpad { i8*, i32 }
          cleanup
  br label %cleanup2.body

cleanup2.body:                                    ; preds = %.noexc, %cleanup2
  %eh.lpad-body = phi { i8*, i32 } [ %49, %cleanup2 ], [ %46, %.noexc ]
  %50 = extractvalue { i8*, i32 } %eh.lpad-body, 0
  %51 = extractvalue { i8*, i32 } %eh.lpad-body, 1
  %52 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %4, i32 0, i32 0
  store i8* %50, i8** %52, align 8
  %53 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %4, i32 0, i32 1
  store i32 %51, i32* %53, align 8
  br label %bb12

bb8:                                              ; preds = %"_ZN5alloc5boxed12Box$LT$T$GT$3new17h486da4461c2b397bE.exit"
  %54 = bitcast %"Vector<Nat>"* %0 to %"Vector<Nat>::Cons"*, !dbg !528
  %55 = bitcast %"Vector<Nat>::Cons"* %54 to i64**, !dbg !528
  %56 = load i64*, i64** %_9, align 8, !dbg !528
  store i64* %56, i64** %55, align 8, !dbg !528
  %57 = bitcast %"Vector<Nat>"* %0 to %"Vector<Nat>::Cons"*, !dbg !528
  %58 = getelementptr inbounds %"Vector<Nat>::Cons", %"Vector<Nat>::Cons"* %57, i32 0, i32 1, !dbg !528
  %59 = load i64*, i64** %_10, align 8, !dbg !528
  store i64* %59, i64** %58, align 8, !dbg !528
  %60 = bitcast %"Vector<Nat>"* %0 to %"Vector<Nat>::Cons"*, !dbg !528
  %61 = getelementptr inbounds %"Vector<Nat>::Cons", %"Vector<Nat>::Cons"* %60, i32 0, i32 2, !dbg !528
  store %"Vector<Nat>"* %47, %"Vector<Nat>"** %61, align 8, !dbg !528
  %62 = bitcast %"Vector<Nat>"* %vector to i64*, !dbg !509
  call void @_ZN5alloc5alloc8box_free17h487859dd7008df07E(i64* nonnull %62), !dbg !509
  br label %bb9, !dbg !509

bb25:                                             ; preds = %bb13
  %63 = load i8, i8* %_23, align 1, !dbg !509, !range !121
  %64 = trunc i8 %63 to i1, !dbg !509
  br i1 %64, label %bb24, label %bb23, !dbg !509

bb23:                                             ; preds = %bb24, %bb25
  %65 = bitcast %"Vector<Nat>"* %vector to i64*, !dbg !509
  call void @_ZN5alloc5alloc8box_free17h487859dd7008df07E(i64* nonnull %65) #6, !dbg !509
  br label %bb14, !dbg !509

bb24:                                             ; preds = %bb25
  call void @"_ZN4core3ptr56drop_in_place$LT$example..Vector$LT$example..Nat$GT$$GT$17h86962fbc7676f71eE"(%"Vector<Nat>"* %vector) #6, !dbg !509
  br label %bb23, !dbg !509

bb14:                                             ; preds = %bb23
  %66 = load i8, i8* %_24, align 1, !dbg !509, !range !121
  %67 = trunc i8 %66 to i1, !dbg !509
  br i1 %67, label %bb26, label %bb15, !dbg !509

bb15:                                             ; preds = %bb26, %bb14
  %68 = load i8, i8* %_25, align 1, !dbg !529, !range !121
  %69 = trunc i8 %68 to i1, !dbg !529
  br i1 %69, label %bb27, label %bb16, !dbg !529

bb26:                                             ; preds = %bb14
  call void @"_ZN4core3ptr33drop_in_place$LT$example..Nat$GT$17h4500bbe220c40510E"(i64** %n0) #6, !dbg !509
  br label %bb15, !dbg !509

bb16:                                             ; preds = %bb27, %bb15
  %70 = load i8, i8* %_21, align 1, !dbg !529, !range !121
  %71 = trunc i8 %70 to i1, !dbg !529
  br i1 %71, label %bb28, label %bb17, !dbg !529

bb27:                                             ; preds = %bb15
  call void @"_ZN4core3ptr56drop_in_place$LT$example..Vector$LT$example..Nat$GT$$GT$17h86962fbc7676f71eE"(%"Vector<Nat>"* %w) #6, !dbg !529
  br label %bb16, !dbg !529

bb17:                                             ; preds = %cleanup3, %bb28, %bb16
  call void @"_ZN4core3ptr33drop_in_place$LT$example..Nat$GT$17h4500bbe220c40510E"(i64** %_1) #6, !dbg !529
  br label %bb18, !dbg !529

bb28:                                             ; preds = %bb16
  call void @"_ZN4core3ptr33drop_in_place$LT$example..Nat$GT$17h4500bbe220c40510E"(i64** %p) #6, !dbg !529
  br label %bb17, !dbg !529

bb9:                                              ; preds = %bb8
  store i8 0, i8* %_23, align 1, !dbg !509
  store i8 0, i8* %_24, align 1, !dbg !509
  br label %bb19, !dbg !529

bb19:                                             ; preds = %bb3, %bb9
  %72 = load i8, i8* %_21, align 1, !dbg !529, !range !121
  %73 = trunc i8 %72 to i1, !dbg !529
  br i1 %73, label %bb20, label %bb10, !dbg !529

bb10:                                             ; preds = %bb20, %bb19
  call void @"_ZN4core3ptr33drop_in_place$LT$example..Nat$GT$17h4500bbe220c40510E"(i64** %_1), !dbg !529
  br label %bb11, !dbg !529

bb20:                                             ; preds = %bb19
  invoke void @"_ZN4core3ptr33drop_in_place$LT$example..Nat$GT$17h4500bbe220c40510E"(i64** %p)
          to label %bb10 unwind label %cleanup3, !dbg !529

cleanup3:                                         ; preds = %bb20
  %74 = landingpad { i8*, i32 }
          cleanup
  %75 = extractvalue { i8*, i32 } %74, 0
  %76 = extractvalue { i8*, i32 } %74, 1
  %77 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %4, i32 0, i32 0
  store i8* %75, i8** %77, align 8
  %78 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %4, i32 0, i32 1
  store i32 %76, i32* %78, align 8
  br label %bb17

bb18:                                             ; preds = %bb17
  %79 = bitcast { i8*, i32 }* %4 to i8**, !dbg !530
  %80 = load i8*, i8** %79, align 8, !dbg !530
  %81 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %4, i32 0, i32 1, !dbg !530
  %82 = load i32, i32* %81, align 8, !dbg !530
  %83 = insertvalue { i8*, i32 } undef, i8* %80, 0, !dbg !530
  %84 = insertvalue { i8*, i32 } %83, i32 %82, 1, !dbg !530
  resume { i8*, i32 } %84, !dbg !530

bb11:                                             ; preds = %bb10
  ret void, !dbg !531
}

define internal void @_ZN7example7one_vec17h01ca9b473d598827E(%"Vector<Nat>"* noalias nocapture sret(%"Vector<Nat>") dereferenceable(24) %0) unnamed_addr #1 personality i32 (i32, i32, i64, %"unwind::libunwind::_Unwind_Exception"*, %"unwind::libunwind::_Unwind_Context"*)* @rust_eh_personality !dbg !532 {
start:
  %1 = alloca { i8*, i32 }, align 8
  %2 = alloca { i8*, i32 }, align 8
  %_4 = alloca %"Vector<Nat>", align 8
  %_2 = alloca i64*, align 8
  %_1 = alloca i64*, align 8
  %3 = bitcast i64** %_1 to {}**, !dbg !533
  store {}* null, {}** %3, align 8, !dbg !533
  %4 = invoke noalias align 8 i64* @_ZN7example7one_nat17h807de8f0aa557d66E()
          to label %bb1 unwind label %cleanup, !dbg !534

bb1:                                              ; preds = %start
  store i64* %4, i64** %_2, align 8, !dbg !534
  %5 = getelementptr inbounds %"Vector<Nat>", %"Vector<Nat>"* %_4, i32 0, i32 1, !dbg !535
  store {}* null, {}** %5, align 8, !dbg !535
  call void @llvm.experimental.noalias.scope.decl(metadata !536), !dbg !539
  %_4.i = invoke i8* @_ZN5alloc5alloc15exchange_malloc17h93ab00f861f87e18E(i64 24, i64 8)
          to label %"_ZN5alloc5boxed12Box$LT$T$GT$3new17h486da4461c2b397bE.exit" unwind label %cleanup.i, !dbg !540, !noalias !536

cleanup.i:                                        ; preds = %bb1
  %6 = landingpad { i8*, i32 }
          cleanup
  %7 = extractvalue { i8*, i32 } %6, 0
  %8 = extractvalue { i8*, i32 } %6, 1
  %9 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %1, i32 0, i32 0
  store i8* %7, i8** %9, align 8, !noalias !536
  %10 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %1, i32 0, i32 1
  store i32 %8, i32* %10, align 8, !noalias !536
  invoke void @"_ZN4core3ptr56drop_in_place$LT$example..Vector$LT$example..Nat$GT$$GT$17h86962fbc7676f71eE"(%"Vector<Nat>"* %_4) #6
          to label %.noexc unwind label %cleanup1, !dbg !542

.noexc:                                           ; preds = %cleanup.i
  %11 = bitcast { i8*, i32 }* %1 to i8**, !dbg !543
  %12 = load i8*, i8** %11, align 8, !dbg !543, !noalias !536
  %13 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %1, i32 0, i32 1, !dbg !543
  %14 = load i32, i32* %13, align 8, !dbg !543, !noalias !536
  %15 = insertvalue { i8*, i32 } undef, i8* %12, 0, !dbg !543
  %16 = insertvalue { i8*, i32 } %15, i32 %14, 1, !dbg !543
  br label %cleanup1.body

"_ZN5alloc5boxed12Box$LT$T$GT$3new17h486da4461c2b397bE.exit": ; preds = %bb1
  %17 = bitcast i8* %_4.i to %"Vector<Nat>"*, !dbg !540
  %18 = bitcast %"Vector<Nat>"* %_4 to i8*, !dbg !544
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 8 %_4.i, i8* align 8 %18, i64 24, i1 false), !dbg !544
  br label %bb2, !dbg !545

bb4:                                              ; preds = %bb3, %cleanup
  call void @"_ZN4core3ptr33drop_in_place$LT$example..Nat$GT$17h4500bbe220c40510E"(i64** %_1) #6, !dbg !546
  br label %bb5, !dbg !546

cleanup:                                          ; preds = %start
  %19 = landingpad { i8*, i32 }
          cleanup
  %20 = extractvalue { i8*, i32 } %19, 0
  %21 = extractvalue { i8*, i32 } %19, 1
  %22 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %2, i32 0, i32 0
  store i8* %20, i8** %22, align 8
  %23 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %2, i32 0, i32 1
  store i32 %21, i32* %23, align 8
  br label %bb4

bb2:                                              ; preds = %"_ZN5alloc5boxed12Box$LT$T$GT$3new17h486da4461c2b397bE.exit"
  %24 = bitcast %"Vector<Nat>"* %0 to %"Vector<Nat>::Cons"*, !dbg !547
  %25 = bitcast %"Vector<Nat>::Cons"* %24 to i64**, !dbg !547
  %26 = load i64*, i64** %_1, align 8, !dbg !547
  store i64* %26, i64** %25, align 8, !dbg !547
  %27 = bitcast %"Vector<Nat>"* %0 to %"Vector<Nat>::Cons"*, !dbg !547
  %28 = getelementptr inbounds %"Vector<Nat>::Cons", %"Vector<Nat>::Cons"* %27, i32 0, i32 1, !dbg !547
  %29 = load i64*, i64** %_2, align 8, !dbg !547
  store i64* %29, i64** %28, align 8, !dbg !547
  %30 = bitcast %"Vector<Nat>"* %0 to %"Vector<Nat>::Cons"*, !dbg !547
  %31 = getelementptr inbounds %"Vector<Nat>::Cons", %"Vector<Nat>::Cons"* %30, i32 0, i32 2, !dbg !547
  store %"Vector<Nat>"* %17, %"Vector<Nat>"** %31, align 8, !dbg !547
  ret void, !dbg !548

bb3:                                              ; preds = %cleanup1.body
  call void @"_ZN4core3ptr33drop_in_place$LT$example..Nat$GT$17h4500bbe220c40510E"(i64** %_2) #6, !dbg !546
  br label %bb4, !dbg !546

cleanup1:                                         ; preds = %cleanup.i
  %32 = landingpad { i8*, i32 }
          cleanup
  br label %cleanup1.body

cleanup1.body:                                    ; preds = %.noexc, %cleanup1
  %eh.lpad-body = phi { i8*, i32 } [ %32, %cleanup1 ], [ %16, %.noexc ]
  %33 = extractvalue { i8*, i32 } %eh.lpad-body, 0
  %34 = extractvalue { i8*, i32 } %eh.lpad-body, 1
  %35 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %2, i32 0, i32 0
  store i8* %33, i8** %35, align 8
  %36 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %2, i32 0, i32 1
  store i32 %34, i32* %36, align 8
  br label %bb3

bb5:                                              ; preds = %bb4
  %37 = bitcast { i8*, i32 }* %2 to i8**, !dbg !549
  %38 = load i8*, i8** %37, align 8, !dbg !549
  %39 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %2, i32 0, i32 1, !dbg !549
  %40 = load i32, i32* %39, align 8, !dbg !549
  %41 = insertvalue { i8*, i32 } undef, i8* %38, 0, !dbg !549
  %42 = insertvalue { i8*, i32 } %41, i32 %40, 1, !dbg !549
  resume { i8*, i32 } %42, !dbg !549
}

define void @_ZN7example4main17h70feb327c5ad4464E() unnamed_addr #1 personality i32 (i32, i32, i64, %"unwind::libunwind::_Unwind_Exception"*, %"unwind::libunwind::_Unwind_Context"*)* @rust_eh_personality !dbg !550 {
start:
  %0 = alloca { i8*, i32 }, align 8
  %_11 = alloca i8, align 1
  %_10 = alloca i8, align 1
  %_9 = alloca i8, align 1
  %_8 = alloca i8, align 1
  %_7 = alloca %"Vector<Nat>", align 8
  %_6 = alloca %"Vector<Nat>", align 8
  %_4 = alloca i64*, align 8
  %_3 = alloca i64*, align 8
  %_2 = alloca i64*, align 8
  %two_vec = alloca %"Vector<Nat>", align 8
  store i8 0, i8* %_11, align 1, !dbg !551
  store i8 0, i8* %_10, align 1, !dbg !551
  store i8 0, i8* %_8, align 1, !dbg !551
  store i8 0, i8* %_9, align 1, !dbg !551
  store i8 1, i8* %_11, align 1, !dbg !552
  %1 = bitcast i64** %_2 to {}**, !dbg !552
  store {}* null, {}** %1, align 8, !dbg !552
  %2 = invoke noalias align 8 i64* @_ZN7example7one_nat17h807de8f0aa557d66E()
          to label %bb1 unwind label %cleanup, !dbg !553

bb1:                                              ; preds = %start
  store i64* %2, i64** %_4, align 8, !dbg !553
  store i8 1, i8* %_10, align 1, !dbg !554
  %_5 = invoke noalias align 8 i64* @_ZN7example7one_nat17h807de8f0aa557d66E()
          to label %bb2 unwind label %cleanup1, !dbg !554

bb16:                                             ; preds = %bb11, %bb12, %bb13, %bb14, %cleanup
  %3 = load i8, i8* %_11, align 1, !dbg !555, !range !121
  %4 = trunc i8 %3 to i1, !dbg !555
  br i1 %4, label %bb15, label %bb8, !dbg !555

cleanup:                                          ; preds = %start
  %5 = landingpad { i8*, i32 }
          cleanup
  %6 = extractvalue { i8*, i32 } %5, 0
  %7 = extractvalue { i8*, i32 } %5, 1
  %8 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 0
  store i8* %6, i8** %8, align 8
  %9 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1
  store i32 %7, i32* %9, align 8
  br label %bb16

bb2:                                              ; preds = %bb1
  store i8 0, i8* %_10, align 1, !dbg !556
  %10 = load i64*, i64** %_4, align 8, !dbg !556
  %11 = invoke noalias align 8 i64* @_ZN7example3add17h9537c70f390d829dE(i64* noalias align 8 %10, i64* noalias align 8 %_5)
          to label %bb3 unwind label %cleanup1, !dbg !556

bb14:                                             ; preds = %cleanup1
  %12 = load i8, i8* %_10, align 1, !dbg !557, !range !121
  %13 = trunc i8 %12 to i1, !dbg !557
  br i1 %13, label %bb13, label %bb16, !dbg !557

cleanup1:                                         ; preds = %bb2, %bb1
  %14 = landingpad { i8*, i32 }
          cleanup
  %15 = extractvalue { i8*, i32 } %14, 0
  %16 = extractvalue { i8*, i32 } %14, 1
  %17 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 0
  store i8* %15, i8** %17, align 8
  %18 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1
  store i32 %16, i32* %18, align 8
  br label %bb14

bb3:                                              ; preds = %bb2
  store i64* %11, i64** %_3, align 8, !dbg !556
  store i8 1, i8* %_9, align 1, !dbg !557
  store i8 0, i8* %_10, align 1, !dbg !557
  invoke void @_ZN7example7one_vec17h01ca9b473d598827E(%"Vector<Nat>"* noalias nocapture sret(%"Vector<Nat>") dereferenceable(24) %_6)
          to label %bb4 unwind label %cleanup2, !dbg !558

bb13:                                             ; preds = %bb14
  call void @"_ZN4core3ptr33drop_in_place$LT$example..Nat$GT$17h4500bbe220c40510E"(i64** %_4) #6, !dbg !557
  br label %bb16, !dbg !557

bb4:                                              ; preds = %bb3
  store i8 1, i8* %_8, align 1, !dbg !559
  invoke void @_ZN7example7one_vec17h01ca9b473d598827E(%"Vector<Nat>"* noalias nocapture sret(%"Vector<Nat>") dereferenceable(24) %_7)
          to label %bb5 unwind label %cleanup3, !dbg !559

bb12:                                             ; preds = %bb9, %bb10, %cleanup2
  %19 = load i8, i8* %_9, align 1, !dbg !555, !range !121
  %20 = trunc i8 %19 to i1, !dbg !555
  br i1 %20, label %bb11, label %bb16, !dbg !555

cleanup2:                                         ; preds = %bb3
  %21 = landingpad { i8*, i32 }
          cleanup
  %22 = extractvalue { i8*, i32 } %21, 0
  %23 = extractvalue { i8*, i32 } %21, 1
  %24 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 0
  store i8* %22, i8** %24, align 8
  %25 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1
  store i32 %23, i32* %25, align 8
  br label %bb12

bb5:                                              ; preds = %bb4
  store i8 0, i8* %_11, align 1, !dbg !560
  store i8 0, i8* %_9, align 1, !dbg !560
  store i8 0, i8* %_8, align 1, !dbg !560
  %26 = load i64*, i64** %_2, align 8, !dbg !560
  %27 = load i64*, i64** %_3, align 8, !dbg !560
  invoke void @_ZN7example6append17hc9590437c6280dd9E(%"Vector<Nat>"* noalias nocapture sret(%"Vector<Nat>") dereferenceable(24) %two_vec, i64* noalias align 8 %26, i64* noalias align 8 %27, %"Vector<Nat>"* noalias nocapture dereferenceable(24) %_6, %"Vector<Nat>"* noalias nocapture dereferenceable(24) %_7)
          to label %bb6 unwind label %cleanup3, !dbg !560

bb10:                                             ; preds = %cleanup3
  %28 = load i8, i8* %_8, align 1, !dbg !555, !range !121
  %29 = trunc i8 %28 to i1, !dbg !555
  br i1 %29, label %bb9, label %bb12, !dbg !555

cleanup3:                                         ; preds = %bb5, %bb4
  %30 = landingpad { i8*, i32 }
          cleanup
  %31 = extractvalue { i8*, i32 } %30, 0
  %32 = extractvalue { i8*, i32 } %30, 1
  %33 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 0
  store i8* %31, i8** %33, align 8
  %34 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1
  store i32 %32, i32* %34, align 8
  br label %bb10

bb6:                                              ; preds = %bb5
  store i8 0, i8* %_8, align 1, !dbg !555
  store i8 0, i8* %_9, align 1, !dbg !555
  store i8 0, i8* %_11, align 1, !dbg !555
  call void @"_ZN4core3ptr56drop_in_place$LT$example..Vector$LT$example..Nat$GT$$GT$17h86962fbc7676f71eE"(%"Vector<Nat>"* %two_vec), !dbg !561
  br label %bb7, !dbg !561

bb9:                                              ; preds = %bb10
  call void @"_ZN4core3ptr56drop_in_place$LT$example..Vector$LT$example..Nat$GT$$GT$17h86962fbc7676f71eE"(%"Vector<Nat>"* %_6) #6, !dbg !555
  br label %bb12, !dbg !555

bb11:                                             ; preds = %bb12
  call void @"_ZN4core3ptr33drop_in_place$LT$example..Nat$GT$17h4500bbe220c40510E"(i64** %_3) #6, !dbg !555
  br label %bb16, !dbg !555

bb8:                                              ; preds = %bb15, %bb16
  %35 = bitcast { i8*, i32 }* %0 to i8**, !dbg !562
  %36 = load i8*, i8** %35, align 8, !dbg !562
  %37 = getelementptr inbounds { i8*, i32 }, { i8*, i32 }* %0, i32 0, i32 1, !dbg !562
  %38 = load i32, i32* %37, align 8, !dbg !562
  %39 = insertvalue { i8*, i32 } undef, i8* %36, 0, !dbg !562
  %40 = insertvalue { i8*, i32 } %39, i32 %38, 1, !dbg !562
  resume { i8*, i32 } %40, !dbg !562

bb15:                                             ; preds = %bb16
  call void @"_ZN4core3ptr33drop_in_place$LT$example..Nat$GT$17h4500bbe220c40510E"(i64** %_2) #6, !dbg !555
  br label %bb8, !dbg !555

bb7:                                              ; preds = %bb6
  ret void, !dbg !563
}

define internal noalias align 8 i64* @"_ZN51_$LT$example..Nat$u20$as$u20$core..clone..Clone$GT$5clone17hc1da32aed59b143dE"(i64** align 8 dereferenceable(8) %self) unnamed_addr #0 !dbg !564 {
start:
  %_2 = alloca i64*, align 8
  %0 = alloca i64*, align 8
  %1 = bitcast i64** %_2 to i64***, !dbg !566
  store i64** %self, i64*** %1, align 8, !dbg !566
  %2 = bitcast i64** %_2 to i64***, !dbg !566
  %3 = load i64**, i64*** %2, align 8, !dbg !566, !nonnull !5
  %4 = bitcast i64** %3 to {}**, !dbg !566
  %5 = load {}*, {}** %4, align 8, !dbg !566
  %6 = icmp eq {}* %5, null, !dbg !566
  %_4 = select i1 %6, i64 0, i64 1, !dbg !566
  switch i64 %_4, label %bb2 [
    i64 0, label %bb3
    i64 1, label %bb1
  ], !dbg !566

bb2:                                              ; preds = %start
  unreachable, !dbg !566

bb3:                                              ; preds = %start
  %7 = bitcast i64** %0 to {}**, !dbg !566
  store {}* null, {}** %7, align 8, !dbg !566
  br label %bb5, !dbg !566

bb1:                                              ; preds = %start
  %8 = bitcast i64** %_2 to i64***, !dbg !567
  %9 = load i64**, i64*** %8, align 8, !dbg !567, !nonnull !5
  %__self_0 = bitcast i64** %9 to i64***, !dbg !567
  %_6 = call noalias nonnull align 8 i64** @"_ZN69_$LT$alloc..boxed..Box$LT$T$C$A$GT$$u20$as$u20$core..clone..Clone$GT$5clone17he460e5310f703f67E"(i64*** align 8 dereferenceable(8) %__self_0), !dbg !567
  br label %bb4, !dbg !567

bb4:                                              ; preds = %bb1
  %10 = bitcast i64** %0 to i64***, !dbg !566
  store i64** %_6, i64*** %10, align 8, !dbg !566
  br label %bb5, !dbg !568

bb5:                                              ; preds = %bb3, %bb4
  %11 = load i64*, i64** %0, align 8, !dbg !569
  ret i64* %11, !dbg !569
}

declare i32 @rust_eh_personality(i32, i32, i64, %"unwind::libunwind::_Unwind_Exception"*, %"unwind::libunwind::_Unwind_Context"*) unnamed_addr #1

declare void @llvm.memcpy.p0i8.p0i8.i64(i8* noalias nocapture writeonly, i8* noalias nocapture readonly, i64, i1 immarg) #2

declare i8* @__rust_alloc_zeroed(i64, i64) unnamed_addr #3

declare void @_ZN5alloc5alloc18handle_alloc_error17he21d1668e088475cE(i64, i64) unnamed_addr #4

declare noalias i8* @__rust_alloc(i64, i64) unnamed_addr #3

declare void @__rust_dealloc(i8*, i64, i64) unnamed_addr #3

declare void @llvm.experimental.noalias.scope.decl(metadata) #5

attributes #0 = { inlinehint nonlazybind uwtable "probe-stack"="__rust_probestack" "target-cpu"="x86-64" }
attributes #1 = { nonlazybind uwtable "probe-stack"="__rust_probestack" "target-cpu"="x86-64" }
attributes #2 = { argmemonly nofree nounwind willreturn }
attributes #3 = { nounwind nonlazybind uwtable "probe-stack"="__rust_probestack" "target-cpu"="x86-64" }
attributes #4 = { cold noreturn nounwind nonlazybind uwtable "probe-stack"="__rust_probestack" "target-cpu"="x86-64" }
attributes #5 = { inaccessiblememonly nofree nosync nounwind willreturn }
attributes #6 = { noinline }
attributes #7 = { nounwind }
attributes #8 = { noreturn nounwind }