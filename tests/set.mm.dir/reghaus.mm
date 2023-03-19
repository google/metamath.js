include "creg.mm"
include "wcel.mm"
include "cha.mm"
include "ct0.mm"
include "ct1.mm"
include "haust1.mm"
include "t1t0.mm"
include "syl.mm"
include "wa.mm"
include "ckq.mm"
include "cfv.mm"
include "regr1.mm"
include "anim2i.mm"
include "ishaus3.mm"
include "sylibr.mm"
include "expcom.mm"
include "impbid2.mm"

theorem reghaus
  let cJ: class J


  assert |- ( J e. Reg -> ( J e. Haus <-> J e. Kol2 ) )

  proof
    cJ
    creg
    wcel
    #
    cJ
    cha
    wcel
    #
    cJ
    ct0
    wcel
    #
    @1
    cJ
    ct1
    wcel
    @2
    cJ
    haust1
    cJ
    t1t0
    syl
    @2
    @0
    @1
    @2
    @0
    wa
    @2
    cJ
    ckq
    cfv
    cha
    wcel
    #
    wa
    @1
    @0
    @3
    @2
    cJ
    regr1
    anim2i
    cJ
    ishaus3
    sylibr
    expcom
    impbid2
end
