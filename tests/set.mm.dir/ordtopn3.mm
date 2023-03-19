include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "crab.mm"
include "cin.mm"
include "cordt.mm"
include "cfv.mm"
include "inrab.mm"
include "ctop.mm"
include "ctopon.mm"
include "ordttopon.mm"
include "3ad2ant1.mm"
include "topontop.mm"
include "syl.mm"
include "ordtopn1.mm"
include "3adant3.mm"
include "ordtopn2.mm"
include "3adant2.mm"
include "inopn.mm"
include "syl3anc.mm"
include "syl5eqelr.mm"

theorem ordtopn3
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let cX: class X
  let vy: setvar y
  let cP: class P
  assume ordttopon.3: |- X = dom R

  disjoint A x
  disjoint B x
  disjoint R x
  disjoint V x
  disjoint X x
  disjoint x y
  disjoint P x
  disjoint P y
  disjoint R y
  disjoint V y
  disjoint X y
  assert |- ( ( R e. V /\ A e. X /\ B e. X ) -> { x e. X | ( -. x R A /\ -. B R x ) } e. ( ordTop ` R ) )

  proof
    cR
    cV
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    vx
    cv
    #
    cA
    cR
    wbr
    wn
    #
    cB
    @4
    cR
    wbr
    wn
    #
    wa
    vx
    cX
    crab
    @5
    vx
    cX
    crab
    #
    @6
    vx
    cX
    crab
    #
    cin
    #
    cR
    cordt
    cfv
    #
    @5
    @6
    vx
    cX
    inrab
    @3
    @10
    ctop
    wcel
    #
    @7
    @10
    wcel
    #
    @8
    @10
    wcel
    #
    @9
    @10
    wcel
    @3
    @10
    cX
    ctopon
    cfv
    wcel
    #
    @11
    @0
    @1
    @14
    @2
    cR
    cV
    cX
    ordttopon.3
    ordttopon
    3ad2ant1
    cX
    @10
    topontop
    syl
    @0
    @1
    @12
    @2
    vx
    cA
    cR
    cV
    cX
    ordttopon.3
    ordtopn1
    3adant3
    @0
    @2
    @13
    @1
    vx
    cB
    cR
    cV
    cX
    ordttopon.3
    ordtopn2
    3adant2
    @7
    @8
    @10
    inopn
    syl3anc
    syl5eqelr
end
