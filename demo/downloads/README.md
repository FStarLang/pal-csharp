# Verified async downloads

A second demonstrator, independent of Petstore: two real HTTP streams fill
separate buffers concurrently. The download loops are ordinary annotated C#,
translated by palcs and checked by Pulse. The page displays byte counts,
SHA-256 digests, and checks against the configured fixture contents.

## Build and check

After the repository toolchain is installed:

```sh
make downloads-demo
```

This builds the tools and support library, verifies `Verified/`, builds the
web app, and runs the real-HTTP integration tests. It is also part of `make test`.
The smaller commands are:

```sh
make -C test/task_ownership       # language examples, including controlled suspension
make -C demo/downloads/Verified  # translate + verify the streaming core
make -C demo/downloads test      # build + isolated HTTP integration checks
```

The HTTP tests start two loopback servers on dynamically allocated ports and
stop them in `finally`; no server or downloaded file is left behind.

## Run the page

In two terminals, from the repository root:

```sh
dotnet run --project demo/downloads/Web/Downloads.Web.csproj -- --fixture=true --urls http://127.0.0.1:5081
dotnet run --project demo/downloads/Web/Downloads.Web.csproj -- --urls http://127.0.0.1:5080
```

Open <http://127.0.0.1:5080> and click **Fetch both files**. The fixture streams
`amber.bin` (4096 bytes) and `blue.bin` (6144 bytes) in small chunks. These are
generated test bytes, not external assets. The web app accepts no user-supplied
download URL. `--FixtureBase=http://127.0.0.1:5081/` changes the configured
fixture server; redirects are disabled, and each file is limited to 1 MiB.

## The proof

`Transfers.Download(source, target)` returns a task with a deferred contract:

- `Source.At(source, n)`: the source cursor has advanced to the returned count.
- `Input.Prefix(source.Content, Contents(target), n)`: `n` fits both sequences,
  and every byte of the returned prefix equals the corresponding source byte.
- `n == target.Length || n == source.Content.Length`: the destination is full,
  or the source is exhausted.

Each `Input.Read` consumes the source and buffer permissions. Its task owns
them until await, which returns the advanced source and extended byte prefix.
The loop invariant composes this across any sequence of short reads. It is a
divergent computation: neither networking nor scheduling is claimed to terminate.

`Transfers.Pair` additionally verifies two outstanding downloads with disjoint
buffers, awaits them in reverse order, and proves full contents and the combined
byte count when each buffer is sized to its source. The integration test runs
this exact method against gated HTTP streams.

The web request coordinator uses `Task.WhenAll` over the individually verified
downloads. This deliberately keeps fault recovery outside the current verified
fragment: WhenAll drains both children before their responses are disposed,
including on failure. Request cancellation and a 30-second deadline cancel reads.
Failures publish an HTTP 502 problem, not a partial completed-download summary.

## Evaluation, not just async syntax

The fixture's gates flush response headers but withhold all bytes. Before
releasing either gate, the test checks that **both verified operations have
started an actual stream read**, and that their combined task is incomplete.
This would fail for sequential download/await code. No sleeps are used to decide
whether that concurrency property holds.

The tests also cover exact bytes, a destination smaller than its source, EOF
before buffer capacity, an empty response, cancellation of both pending reads,
truncated HTTP responses, web checksum/count reporting, and an unavailable
fixture. The language tests separately reject premature buffer access,
overlapping writable ownership, duplicate await through an alias, and a false
promised result.

## What is trusted

- `Pulse.Lib.CSharp.Async.fsti` specifies CLR task ownership and normal
  completion. It does not verify the CLR scheduler. Faulted/cancelled awaits
  have no normal return in this model; verified catch/recovery is not supported.
- `DownloadIO.read` is an explicit assumption about successful `Stream.ReadAsync`:
  it advances the source, preserves/extends the byte prefix, and returns zero
  exactly at EOF. The `[Implements]` binder's contract is checked against this
  assumption. Both this source and the task boundary are in the trust manifest.
- The `Source` SpecType binding identifies the logical bytes/cursor with the HTTP
  response stream. Opening and disposing a response, content-length validation,
  HTTP framing, and the read-count instrumentation are runtime code, not proofs.
- The UI, `Task.WhenAll` recovery coordinator, expected fixture data, and SHA-256
  are unverified. The proof establishes byte-prefix correctness against the
  stream model, not SHA-256 correctness or remote authenticity.

Petstore remains unchanged.
