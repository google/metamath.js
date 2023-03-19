include "ctg.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "cdm.mm"
include "wi.mm"
include "elfvdm.mm"
include "wral.mm"
include "eltg2b.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "rspccv.mm"
include "syl6bi.mm"
include "mpcom.mm"
include "imp.mm"

theorem tg2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cJ: class J
  let cV: class V

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint C y
  assert |- ( ( A e. ( topGen ` B ) /\ C e. A ) -> E. x e. B ( C e. x /\ x C_ A ) )

  proof
    cA
    cB
    ctg
    cfv
    wcel
    #
    cC
    cA
    wcel
    #
    cC
    vx
    cv
    #
    wcel
    #
    @2
    cA
    wss
    #
    wa
    #
    vx
    cB
    wrex
    #
    cB
    ctg
    cdm
    #
    wcel
    #
    @0
    @1
    @6
    wi
    #
    cA
    cB
    ctg
    elfvdm
    @8
    @0
    vy
    cv
    #
    @2
    wcel
    #
    @4
    wa
    #
    vx
    cB
    wrex
    #
    vy
    cA
    wral
    @9
    vy
    vx
    cA
    cB
    @7
    eltg2b
    @13
    @6
    vy
    cC
    cA
    @10
    cC
    wceq
    #
    @12
    @5
    vx
    cB
    @14
    @11
    @3
    @4
    @10
    cC
    @2
    eleq1
    anbi1d
    rexbidv
    rspccv
    syl6bi
    mpcom
    imp
end
