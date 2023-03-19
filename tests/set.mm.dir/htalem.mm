include "wwe.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "crio.mm"
include "wreu.mm"
include "wcel.mm"
include "cvv.mm"
include "wss.mm"
include "simpl.mm"
include "a1i.mm"
include "ssid.mm"
include "simpr.mm"
include "wereu.mm"
include "syl13anc.mm"
include "riotacl.mm"
include "syl.mm"
include "syl5eqel.mm"

theorem htalem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  assume htalem.1: |- A e. _V
  assume htalem.2: |- B = ( iota_ x e. A A. y e. A -. y R x )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint R x
  disjoint R y
  assert |- ( ( R We A /\ A =/= (/) ) -> B e. A )

  proof
    cA
    cR
    wwe
    #
    cA
    c0
    wne
    #
    wa
    #
    cB
    vy
    cv
    vx
    cv
    cR
    wbr
    wn
    vy
    cA
    wral
    #
    vx
    cA
    crio
    #
    cA
    htalem.2
    @2
    @3
    vx
    cA
    wreu
    #
    @4
    cA
    wcel
    @2
    @0
    cA
    cvv
    wcel
    #
    cA
    cA
    wss
    #
    @1
    @5
    @0
    @1
    simpl
    @6
    @2
    htalem.1
    a1i
    @7
    @2
    cA
    ssid
    a1i
    @0
    @1
    simpr
    vx
    vy
    cA
    cA
    cR
    cvv
    wereu
    syl13anc
    @3
    vx
    cA
    riotacl
    syl
    syl5eqel
end
