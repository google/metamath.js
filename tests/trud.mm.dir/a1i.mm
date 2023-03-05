include "kt.mm"
include "ax-trud.mm"
include "syl.mm"

theorem a1i
  let ta: term A
  let tr: term R
  assume ax-trud.1: |- R : bool
  assume ax-a1i.2: |- T. |= A


  assert |- R |= A

  step 0) tr(): term R
  step 1) kt(): term T.
  step 2) ta(): term A
  step 3) tr(): term R
  step 4) ax-trud.1(): |- R : bool
  step 5) ax-trud(3,4): |- R |= T.
  step 6) ax-a1i.2(): |- T. |= A
  step 7) syl(0,1,2,5,6): |- R |= A
end
