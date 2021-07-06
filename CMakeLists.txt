set( LLVM_LINK_COMPONENTS
  ${LLVM_TARGETS_TO_BUILD}
  Option
  Support
  )

add_clang_executable(framaCIRGen
  DescentParse.cpp
  ACSLCodeAnnotation.cpp
  ACSLComment.cpp
  ACSLComponent.cpp
  ACSLFunctionContract.cpp
  ACSLGlobalAnnotation.cpp
  ACSLLexer.cpp
  ACSLLogicType.cpp
  ACSLLoopAnnotation.cpp
  ACSLParser.cpp
  ACSLStatementAnnotation.cpp
  ACSLTermOrPredicate.cpp
  ACSLToken.cpp
  Clang_utils.cpp
  ClangVisitor.cpp
  RTTITable.cpp
  VisitTable.cpp
  FramaCIRGen.cpp
  intermediate_format.c
  )

if (CLANG_VERSION VERSION_LESS 6.0.0)
target_link_libraries(framaCIRGen
  clangAnalysis
  clangAST
  clangBasic
  clangDriver
  clangEdit
  clangFrontend
  clangLex
  clangParse
  clangSema
  clangSerialization
  clangTooling
  LLVMBitReader
  LLVMMCParser
  LLVMOption
  )
else()
target_link_libraries(framaCIRGen
  PRIVATE
  clangAnalysis
  clangAST
  clangBasic
  clangDriver
  clangEdit
  clangFrontend
  clangLex
  clangParse
  clangSema
  clangSerialization
  clangTooling
  )
endif()

install(TARGETS framaCIRGen
  RUNTIME DESTINATION bin)
