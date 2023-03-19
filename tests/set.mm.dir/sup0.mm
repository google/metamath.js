include "wor.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wa.mm"
include "wreu.mm"
include "w3a.mm"
include "c0.mm"
include "csup.mm"
include "crio.mm"
include "wceq.mm"
include "sup0riota.mm"
include "3ad2ant1.mm"
include "simp2r.mm"
include "wb.mm"
include "simpl.mm"
include "anim1i.mm"
include "3adant1.mm"
include "breq2.mm"
include "notbid.mm"
include "ralbidv.mm"
include "riota2.mm"
include "syl.mm"
include "mpbid.mm"
include "eqtrd.mm"

theorem sup0
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cX: class X
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint X x
  disjoint X y
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint R z
  assert |- ( ( R Or A /\ ( X e. A /\ A. y e. A -. y R X ) /\ E! x e. A A. y e. A -. y R x ) -> sup ( (/) , A , R ) = X )

  proof
    cA
    cR
    wor
    #
    cX
    cA
    wcel
    #
    vy
    cv
    #
    cX
    cR
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    wa
    #
    @2
    vx
    cv
    #
    cR
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    vx
    cA
    wreu
    #
    w3a
    #
    c0
    cA
    cR
    csup
    #
    @10
    vx
    cA
    crio
    #
    cX
    @0
    @6
    @13
    @14
    wceq
    @11
    vx
    vy
    cA
    cR
    sup0riota
    3ad2ant1
    @12
    @5
    @14
    cX
    wceq
    #
    @0
    @1
    @5
    @11
    simp2r
    @12
    @1
    @11
    wa
    #
    @5
    @15
    wb
    @6
    @11
    @16
    @0
    @6
    @1
    @11
    @1
    @5
    simpl
    anim1i
    3adant1
    @10
    @5
    vx
    cA
    cX
    @7
    cX
    wceq
    #
    @9
    @4
    vy
    cA
    @17
    @8
    @3
    @7
    cX
    @2
    cR
    breq2
    notbid
    ralbidv
    riota2
    syl
    mpbid
    eqtrd
end
