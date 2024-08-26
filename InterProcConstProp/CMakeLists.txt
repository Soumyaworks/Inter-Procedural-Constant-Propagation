# If we don't need RTTI or EH, there's no reason to export anything
# from the hello plugin.

add_llvm_library(LLVMCons_inter MODULE BUILDTREE_ONLY
  cons_eval.cpp

  DEPENDS
  intrinsics_gen
  PLUGIN_TOOL
  opt
  )