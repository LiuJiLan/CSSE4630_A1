@echo off
chcp 65001 > nul

set JAVA_HOME=C:\Users\LiuJiLan\.jdks\ms-21.0.7
set PATH=%JAVA_HOME%\bin;%PATH%

set JAVA_OPTS=-Dfile.encoding=UTF-8
sbt "runMain tip.Tip %*"
