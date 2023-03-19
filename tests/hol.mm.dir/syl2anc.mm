include "kct.mm"
include "jca.mm"
include "syl.mm"

theorem syl2anc
  param ta: term A
  param tr: term R
  param ts: term S
  param tt: term T
  assume syl2anc.1: |- R |= S
  assume syl2anc.2: |- R |= T
  assume syl2anc.3: |- ( S , T ) |= A


  assert |- R |= A

  proof
    tr
    ts
    tt
    kct
    ta
    tr
    ts
    tt
    syl2anc.1
    syl2anc.2
    jca
    syl2anc.3
    syl
end
