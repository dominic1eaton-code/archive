#

Get-ChildItem -Filter *.zip -Recurse | Expand-Archive -DestinationPath {Split-Path $_.FullName} -Force
Get-ChildItem -Filter *.zip -Recurse | Expand-Archive -DestinationPath . -Force


