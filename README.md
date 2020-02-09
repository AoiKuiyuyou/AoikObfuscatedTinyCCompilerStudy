# AoikObfuscatedTinyCCompilerStudy
Added comments and prints to
[Obfuscated Tiny C Compiler](https://bellard.org/otcc/)'s
[otccelfn.c](/src/otccelfn.c) file.

**Compile otccelfn.c:**
```
# CentOS 7
yum install -y glibc-devel glibc-devel.i686

yum install -y libgcc.x86_64 libgcc.i686

gcc -m32 -march=i386 -O2 -w src/otccelfn.c -o otccelfn
```

**Use otccelfn to compile example otccex.c:**
```
chmod 500 otccelfn

./otccelfn src/otccex.c otccex

chmod 500 otccex

./otccex 5
```
