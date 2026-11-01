import Cache.Hashing
open Cache IO Hashing System in
def main (args : List String) : IO Unit := CacheM.run do
  let roots ← parseArgs ("get" :: args)
  let memo ← getHashMemo roots
  let selected ← memo.filterByRootModules roots.keys
  for (name, hash) in selected.toList do
    IO.println s!"{name}\t{hash.asLTar}"
