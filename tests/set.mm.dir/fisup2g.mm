include "wor.mm"
include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wreu.mm"
include "soss.mm"
include "simp1.mm"
include "fisupg.mm"
include "supeu.mm"
include "3exp.mm"
include "syl6.mm"
include "com4l.mm"
include "3imp2.mm"
include "reurex.mm"
include "breq2.mm"
include "rspcev.mm"
include "ex.mm"
include "ralrimivw.mm"
include "a1d.mm"
include "anim2d.mm"
include "reximia.mm"
include "3syl.mm"

theorem fisup2g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cR: class R

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint B x
  disjoint B y
  disjoint B z
  assert |- ( ( R Or A /\ ( B e. Fin /\ B =/= (/) /\ B C_ A ) ) -> E. x e. B ( A. y e. B -. x R y /\ A. y e. A ( y R x -> E. z e. B y R z ) ) )

  proof
    cA
    cR
    wor
    #
    cB
    cfn
    wcel
    #
    cB
    c0
    wne
    #
    cB
    cA
    wss
    #
    w3a
    wa
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    wn
    vy
    cB
    wral
    #
    @5
    @4
    cR
    wbr
    #
    @5
    vz
    cv
    #
    cR
    wbr
    #
    vz
    cB
    wrex
    #
    wi
    #
    vy
    cB
    wral
    #
    wa
    #
    vx
    cB
    wreu
    #
    @13
    vx
    cB
    wrex
    @6
    @11
    vy
    cA
    wral
    #
    wa
    #
    vx
    cB
    wrex
    @0
    @1
    @2
    @3
    @14
    @3
    @0
    @1
    @2
    @14
    @3
    @0
    cB
    cR
    wor
    #
    @1
    @2
    @14
    wi
    wi
    cB
    cA
    cR
    soss
    @17
    @1
    @2
    @14
    @17
    @1
    @2
    w3a
    vx
    vy
    vz
    cB
    cB
    cR
    @17
    @1
    @2
    simp1
    vx
    vy
    vz
    cB
    cR
    fisupg
    supeu
    3exp
    syl6
    com4l
    3imp2
    @13
    vx
    cB
    reurex
    @13
    @16
    vx
    cB
    @4
    cB
    wcel
    #
    @12
    @15
    @6
    @18
    @15
    @12
    @18
    @11
    vy
    cA
    @18
    @7
    @10
    @9
    @7
    vz
    @4
    cB
    @8
    @4
    @5
    cR
    breq2
    rspcev
    ex
    ralrimivw
    a1d
    anim2d
    reximia
    3syl
end
