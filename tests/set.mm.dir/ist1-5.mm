include "ct1.mm"
include "t1t0.mm"
include "ckq.mm"
include "cfv.mm"
include "t1hmph.mm"
include "ist1-5lem.mm"

theorem ist1-5
  let cJ: class J


  assert |- ( J e. Fre <-> ( J e. Kol2 /\ ( KQ ` J ) e. Fre ) )

  proof
    ct1
    cJ
    cJ
    t1t0
    cJ
    cJ
    ckq
    cfv
    #
    t1hmph
    @0
    cJ
    t1hmph
    ist1-5lem
end
