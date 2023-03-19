include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "crab.mm"
include "cin.mm"
include "cordt.mm"
include "cfv.mm"
include "ccld.mm"
include "inrab.mm"
include "ordtcld2.mm"
include "3adant3.mm"
include "ordtcld1.mm"
include "3adant2.mm"
include "incld.mm"
include "syl2anc.mm"
include "syl5eqelr.mm"

theorem ordtcld3
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
  assert |- ( ( R e. V /\ A e. X /\ B e. X ) -> { x e. X | ( A R x /\ x R B ) } e. ( Clsd ` ( ordTop ` R ) ) )

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
    cA
    vx
    cv
    #
    cR
    wbr
    #
    @4
    cB
    cR
    wbr
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
    ccld
    cfv
    #
    @5
    @6
    vx
    cX
    inrab
    @3
    @7
    @11
    wcel
    #
    @8
    @11
    wcel
    #
    @9
    @11
    wcel
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
    ordtcld2
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
    ordtcld1
    3adant2
    @7
    @8
    @10
    incld
    syl2anc
    syl5eqelr
end
