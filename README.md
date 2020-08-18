# VirtAnalyzer
VirtAnalyzer is implemented as an IDAPython script (recover_virtual_inheritance.py). It recovers virtual inheritance tree from a C++ binary.

## How to run the script
recover_virtual_inheritance.py (for Itanium or MSVC ABI) can be executed by doing one of the following:

Execute `runscript('recover_virtual_inheritance.py')` from IDAPro console. This should be full path to the script.

or

Go to File -> Script file... and select recover_virtual_inheritance.py

Note: By default, both versions of recover_virtual_inheritance.py are set for 64-bit binaries. To make it work for a 32-bit binary, set the global variable `DWORD_SIZE` to 4.

## Binaries
The binaries folder consist of two zip files, one contains Itanium ABI binaries and the other contains MSVC binaries. The Itanium ABI binaries are C++ binaries compiled with GCC 7.3.0. The MSVC binaries are dlls recovered from a Windows 10 computer. The Itanium ABI zip file contains only 64-bit binaries, while the MSVC ABI zip file contains both 32-bit and 64-bit binaries. 
