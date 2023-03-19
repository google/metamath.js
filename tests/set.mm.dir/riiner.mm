include "wer.mm"
include "wral.mm"
include "cxp.mm"
include "ciin.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "xpider.mm"
include "wb.mm"
include "riin0.mm"
include "adantl.mm"
include "ereq1.mm"
include "syl.mm"
include "mpbiri.mm"
include "wne.mm"
include "iiner.mm"
include "ancoms.mm"
include "wss.mm"
include "erssxp.mm"
include "ralimi.mm"
include "riinn0.mm"
include "sylan.mm"
include "mpbird.mm"
include "pm2.61dane.mm"

theorem riiner
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w

  disjoint A x
  disjoint B x
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint A v
  disjoint w x
  disjoint A w
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint R u
  disjoint R v
  disjoint R w
  assert |- ( A. x e. A R Er B -> ( ( B X. B ) i^i |^|_ x e. A R ) Er B )

  proof
    cB
    cR
    wer
    #
    vx
    cA
    wral
    #
    cB
    cB
    cB
    cxp
    #
    vx
    cA
    cR
    ciin
    #
    cin
    #
    wer
    #
    cA
    c0
    @1
    cA
    c0
    wceq
    #
    wa
    #
    @5
    cB
    @2
    wer
    #
    cB
    xpider
    @7
    @4
    @2
    wceq
    #
    @5
    @8
    wb
    @6
    @9
    @1
    vx
    @2
    cR
    cA
    riin0
    adantl
    cB
    @4
    @2
    ereq1
    syl
    mpbiri
    @1
    cA
    c0
    wne
    #
    wa
    #
    @5
    cB
    @3
    wer
    #
    @10
    @1
    @12
    vx
    cA
    cB
    cR
    iiner
    ancoms
    @11
    @4
    @3
    wceq
    #
    @5
    @12
    wb
    @1
    cR
    @2
    wss
    #
    vx
    cA
    wral
    @10
    @13
    @0
    @14
    vx
    cA
    cB
    cR
    erssxp
    ralimi
    vx
    @2
    cR
    cA
    riinn0
    sylan
    cB
    @4
    @3
    ereq1
    syl
    mpbird
    pm2.61dane
end
