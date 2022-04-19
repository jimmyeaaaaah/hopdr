
'''
hflmc2/benchmark/inputs/mochi2//a-copy-print.in
thread 'main' panicked at 'assertion failed: body.predicate != p || args.is_none()', src/solver/interpolation.rs:241:9
note: run with `RUST_BACKTRACE=1` environment variable to display a backtrace
\n
'''

with open("errors") as f:
  l = f.read().strip("\n").split("\n")


results = []
idx = 0
while idx < len(l):
  tit = l[idx]
  res = l[idx + 1]
  reason = None
  #print(tit, res)
  if res == "\\n":
    result = "timeout"
  elif res == "Valid":
    result = "valid"
  elif res == "Invalid":
    result = "invalid"
  else:
    result = "error"
    reason = res 
  if tit.endswith(".in"):
    #print(tit, result, reason)
    results.append((tit, result, reason))
  while idx < len(l):
    idx += 1
    if l[idx] == "\\n":
      idx += 1
      break

# stat
d = dict()
for (_, r, _) in results:
  v = d.get(r, 0)
  d[r] = v + 1

for key in ["valid", "invalid", "timeout", "error"]:
  print(f"{key:8}: {d.get(key, 0)}")


d = dict()
for (tit, r, reason) in results:
  if r == "error":
    v = d.get(reason, [])
    v.append(tit)
    d[reason] = v

print(f"There are {len(d)} kinds of bugs")
for (key, l) in d.items():
  print(f"{key}")
  for x in l:
    print(f"- {x}")


  
