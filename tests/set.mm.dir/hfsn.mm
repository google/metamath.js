include "chf.mm"
include "wcel.mm"
include "csn.mm"
include "crnk.mm"
include "cfv.mm"
include "com.mm"
include "csuc.mm"
include "ranksng.mm"
include "elhf2g.mm"
include "ibi.mm"
include "peano2.mm"
include "syl.mm"
include "eqeltrd.mm"
include "snex.mm"
include "elhf2.mm"
include "sylibr.mm"

theorem hfsn
  let cA: class A


  assert |- ( A e. Hf -> { A } e. Hf )

  proof
    cA
    chf
    wcel
    #
    cA
    csn
    #
    crnk
    cfv
    #
    com
    wcel
    @1
    chf
    wcel
    @0
    @2
    cA
    crnk
    cfv
    #
    csuc
    #
    com
    cA
    chf
    ranksng
    @0
    @3
    com
    wcel
    #
    @4
    com
    wcel
    @0
    @5
    cA
    chf
    elhf2g
    ibi
    @3
    peano2
    syl
    eqeltrd
    @1
    cA
    snex
    elhf2
    sylibr
end
