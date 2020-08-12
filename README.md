# VirtAnalyzer
VirtAnalyzer is implemented as an IDAPython script (recover_virtual_inheritance.py). It recovers virtual inheritance tree from a C++ binary.

## How to run the script
recover_virtual_inheritance.py can be executed by doing one of the following:

Execute `runscript('recover_virtual_inheritance.py')` from IDAPro console. This should be full path to the script.

or

Go to File -> Script file... and select recover_virtual_inheritance.py

## Binaries
The binaries that we have tested VirtAnalyzer on can be found in the binaries/ directory. They are C++ binaries compiled with GCC 7.3.0.
