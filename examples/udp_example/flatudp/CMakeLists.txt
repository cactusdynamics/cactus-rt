# Header only library because it is a template class..
add_library(flatudp INTERFACE)

target_include_directories(flatudp
  INTERFACE
  .
)

target_compile_features(flatudp
  INTERFACE
  cxx_std_20
)
