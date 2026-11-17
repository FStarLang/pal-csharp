.PHONY: all verify build test clean
all: verify test

verify:
	$(MAKE) -C Verified

build:
	@mkdir -p ../../src/Pal.Annotations/obj
	flock --close ../../src/Pal.Annotations/obj/pal-tests.lock dotnet build Web/Downloads.Web.csproj --nologo -v:q
	flock --close ../../src/Pal.Annotations/obj/pal-tests.lock dotnet build Tests/Downloads.Tests.csproj --nologo -v:q

test: build
	python3 test.py

clean:
	$(MAKE) -C Verified clean
	dotnet clean Web/Downloads.Web.csproj --nologo -v:q
	dotnet clean Tests/Downloads.Tests.csproj --nologo -v:q
