include "ctop.mm"
include "wcel.mm"
include "cfn.mm"
include "wral.mm"
include "w3a.mm"
include "ciin.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "riin0.mm"
include "adantl.mm"
include "simpl1.mm"
include "topopn.mm"
include "syl.mm"
include "eqeltrd.mm"
include "wne.mm"
include "wss.mm"
include "wi.mm"
include "eltopss.mm"
include "ex.mm"
include "adantr.mm"
include "ralimdv.mm"
include "3impia.mm"
include "riinn0.mm"
include "sylan.mm"
include "iinopn.mm"
include "3exp2.mm"
include "com34.mm"
include "3imp1.mm"
include "pm2.61dane.mm"

theorem riinopn
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cJ: class J
  let cX: class X
  assume 1open.1: |- X = U. J

  disjoint A x
  disjoint J x
  disjoint X x
  assert |- ( ( J e. Top /\ A e. Fin /\ A. x e. A B e. J ) -> ( X i^i |^|_ x e. A B ) e. J )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cfn
    wcel
    #
    cB
    cJ
    wcel
    #
    vx
    cA
    wral
    #
    w3a
    #
    cX
    vx
    cA
    cB
    ciin
    #
    cin
    #
    cJ
    wcel
    cA
    c0
    @4
    cA
    c0
    wceq
    #
    wa
    #
    @6
    cX
    cJ
    @7
    @6
    cX
    wceq
    @4
    vx
    cX
    cB
    cA
    riin0
    adantl
    @8
    @0
    cX
    cJ
    wcel
    @0
    @1
    @3
    @7
    simpl1
    cJ
    cX
    1open.1
    topopn
    syl
    eqeltrd
    @4
    cA
    c0
    wne
    #
    wa
    @6
    @5
    cJ
    @4
    cB
    cX
    wss
    #
    vx
    cA
    wral
    #
    @9
    @6
    @5
    wceq
    @0
    @1
    @3
    @11
    @0
    @1
    wa
    @2
    @10
    vx
    cA
    @0
    @2
    @10
    wi
    @1
    @0
    @2
    @10
    cB
    cJ
    cX
    1open.1
    eltopss
    ex
    adantr
    ralimdv
    3impia
    vx
    cX
    cB
    cA
    riinn0
    sylan
    @0
    @1
    @3
    @9
    @5
    cJ
    wcel
    #
    @0
    @1
    @9
    @3
    @12
    @0
    @1
    @9
    @3
    @12
    vx
    cA
    cB
    cJ
    iinopn
    3exp2
    com34
    3imp1
    eqeltrd
    pm2.61dane
end
