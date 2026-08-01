# Checks the core invariant: annotated C# compiles, runs unchanged, and leaves
# no trace in the IL when PAL is not defined.

.PHONY: all clean

all:
	@dotnet run -v q --nologo --project Erasure.csproj

clean:
	@rm -rf bin obj
