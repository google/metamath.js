include "crab.mm"
include "ciin.mm"
include "cin.mm"
include "wral.mm"
include "wceq.mm"
include "c0.mm"
include "riin0.mm"
include "rzal.mm"
include "ralrimivw.mm"
include "rabid2.mm"
include "sylibr.mm"
include "eqtrd.mm"
include "wne.mm"
include "wss.mm"
include "ssrab2.mm"
include "rgenw.mm"
include "riinn0.mm"
include "mpan.mm"
include "iinrab.mm"
include "pm2.61ine.mm"

theorem riinrab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cX: class X
  let cB: class B

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint X x
  disjoint X y
  disjoint B x
  assert |- ( A i^i |^|_ x e. X { y e. A | ph } ) = { y e. A | A. x e. X ph }

  proof
    cA
    vx
    cX
    wph
    vy
    cA
    crab
    #
    ciin
    #
    cin
    #
    wph
    vx
    cX
    wral
    #
    vy
    cA
    crab
    #
    wceq
    cX
    c0
    cX
    c0
    wceq
    #
    @2
    cA
    @4
    vx
    cA
    @0
    cX
    riin0
    @5
    @3
    vy
    cA
    wral
    cA
    @4
    wceq
    @5
    @3
    vy
    cA
    wph
    vx
    cX
    rzal
    ralrimivw
    @3
    vy
    cA
    rabid2
    sylibr
    eqtrd
    cX
    c0
    wne
    #
    @2
    @1
    @4
    @0
    cA
    wss
    #
    vx
    cX
    wral
    @6
    @2
    @1
    wceq
    @7
    vx
    cX
    wph
    vy
    cA
    ssrab2
    rgenw
    vx
    cA
    @0
    cX
    riinn0
    mpan
    wph
    vx
    vy
    cX
    cA
    iinrab
    eqtrd
    pm2.61ine
end
