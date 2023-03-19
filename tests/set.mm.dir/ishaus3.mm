include "cha.mm"
include "wcel.mm"
include "ct1.mm"
include "ct0.mm"
include "haust1.mm"
include "t1t0.mm"
include "syl.mm"
include "ckq.mm"
include "cfv.mm"
include "haushmph.mm"
include "ist1-5lem.mm"

theorem ishaus3
  let cJ: class J


  assert |- ( J e. Haus <-> ( J e. Kol2 /\ ( KQ ` J ) e. Haus ) )

  proof
    cha
    cJ
    cJ
    cha
    wcel
    cJ
    ct1
    wcel
    cJ
    ct0
    wcel
    cJ
    haust1
    cJ
    t1t0
    syl
    cJ
    cJ
    ckq
    cfv
    #
    haushmph
    @0
    cJ
    haushmph
    ist1-5lem
end
