rem
rem
rem

@REM mkdir AVCrowd
@REM tar -xvf AVCrowd.zip -C AVCrowd

@ECHO OFF
setlocal enabledelayedexpansion
set ZIP_DIR="C:\Users\domin\OneDrive\Desktop\files\desktop\pub"
for %%f in (%ZIP_DIR%\*.zip) do (
  set /p val=<%%f
  echo "fullname: %%f"
  echo "name: %%~nf"
  echo "contents: !val!"
  mkdir "%%~nf"
  tar -xvf "%%~nf".zip -C "%%~nf"
)