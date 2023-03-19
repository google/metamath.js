include "chf.mm"
include "wcel.mm"
include "cpw.mm"
include "crnk.mm"
include "cfv.mm"
include "com.mm"
include "csuc.mm"
include "rankpwg.mm"
include "elhf2g.mm"
include "ibi.mm"
include "peano2.mm"
include "syl.mm"
include "eqeltrd.mm"
include "cvv.mm"
include "wb.mm"
include "pwexg.mm"
include "mpbird.mm"

theorem hfpw
  let cA: class A


  assert |- ( A e. Hf -> ~P A e. Hf )

  proof
    cA
    chf
    wcel
    #
    cA
    cpw
    #
    chf
    wcel
    #
    @1
    crnk
    cfv
    #
    com
    wcel
    #
    @0
    @3
    cA
    crnk
    cfv
    #
    csuc
    #
    com
    cA
    chf
    rankpwg
    @0
    @5
    com
    wcel
    #
    @6
    com
    wcel
    @0
    @7
    cA
    chf
    elhf2g
    ibi
    @5
    peano2
    syl
    eqeltrd
    @0
    @1
    cvv
    wcel
    @2
    @4
    wb
    cA
    chf
    pwexg
    @1
    cvv
    elhf2g
    syl
    mpbird
end
