.PHONY: all clean
all:
	MSBUILDDISABLENODEREUSE=1 DOTNET_CLI_USE_MSBUILD_SERVER=0 dotnet run \
	  --project Classifier.csproj --disable-build-servers -p:UseSharedCompilation=false

clean:
	dotnet clean Classifier.csproj --disable-build-servers
