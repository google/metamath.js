include "kct.mm"
include "jca.mm"
include "syl.mm"

theorem syl2anc
  let ta: term A
  let tr: term R
  let ts: term S
  let tt: term T
  assume syl2anc.1: |- R |= S
  assume syl2anc.2: |- R |= T
  assume syl2anc.3: |- ( S , T ) |= A


  assert |- R |= A

  step 0) tr(): term R
  step 1) ts(): term S
  step 2) tt(): term T
  step 3) kct(1, 2): term ( S , T )
  step 4) ta(): term A
  step 5) tr(): term R
  step 6) ts(): term S
  step 7) tt(): term T
  step 8) syl2anc.1(): |- R |= S
  step 9) syl2anc.2(): |- R |= T
  step 10) jca(5, 6, 7, 8, 9): |- R |= ( S , T )
  step 11) syl2anc.3(): |- ( S , T ) |= A
  step 12) syl(0, 3, 4, 10, 11): |- R |= A
end
