include "wcel.mm"
include "ct0.mm"
include "ckq.mm"
include "cfv.mm"
include "wa.mm"
include "chmph.mm"
include "wbr.mm"
include "kqhmph.mm"
include "sylib.mm"
include "mpcom.mm"
include "jca.mm"
include "wi.mm"
include "hmphsym.mm"
include "sylbi.mm"
include "syl.mm"
include "imp.mm"
include "impbii.mm"

theorem ist1-5lem
  let cA: class A
  let cJ: class J
  assume ist1-5lem.1: |- ( J e. A -> J e. Kol2 )
  assume ist1-5lem.2: |- ( J ~= ( KQ ` J ) -> ( J e. A -> ( KQ ` J ) e. A ) )
  assume ist1-5lem.3: |- ( ( KQ ` J ) ~= J -> ( ( KQ ` J ) e. A -> J e. A ) )


  assert |- ( J e. A <-> ( J e. Kol2 /\ ( KQ ` J ) e. A ) )

  proof
    cJ
    cA
    wcel
    #
    cJ
    ct0
    wcel
    #
    cJ
    ckq
    cfv
    #
    cA
    wcel
    #
    wa
    @0
    @1
    @3
    ist1-5lem.1
    cJ
    @2
    chmph
    wbr
    #
    @0
    @3
    @0
    @1
    @4
    ist1-5lem.1
    cJ
    kqhmph
    #
    sylib
    ist1-5lem.2
    mpcom
    jca
    @1
    @3
    @0
    @1
    @2
    cJ
    chmph
    wbr
    #
    @3
    @0
    wi
    @1
    @4
    @6
    @5
    cJ
    @2
    hmphsym
    sylbi
    ist1-5lem.3
    syl
    imp
    impbii
end
