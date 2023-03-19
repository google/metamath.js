include "csur.mm"
include "wcel.mm"
include "cdm.mm"
include "con0.mm"
include "word.mm"
include "nodmon.mm"
include "eloni.mm"
include "syl.mm"

theorem nodmord
  let cA: class A


  assert |- ( A e. No -> Ord dom A )

  proof
    cA
    csur
    wcel
    cA
    cdm
    #
    con0
    wcel
    @0
    word
    cA
    nodmon
    @0
    eloni
    syl
end
