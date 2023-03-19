include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "ccom.mm"
include "wbr.mm"
include "cv.mm"
include "wex.mm"
include "brcog.mm"
include "wb.mm"
include "cvv.mm"
include "vex.mm"
include "brcnvg.mm"
include "mpan.mm"
include "anbi2d.mm"
include "adantl.mm"
include "exbidv.mm"
include "bitrd.mm"

theorem brcodir
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let cS: class S

  disjoint A z
  disjoint B z
  disjoint R z
  disjoint V z
  disjoint W z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  disjoint S z
  assert |- ( ( A e. V /\ B e. W ) -> ( A ( `' R o. R ) B <-> E. z ( A R z /\ B R z ) ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    cA
    cB
    cR
    ccnv
    #
    cR
    ccom
    wbr
    cA
    vz
    cv
    #
    cR
    wbr
    #
    @4
    cB
    @3
    wbr
    #
    wa
    #
    vz
    wex
    @5
    cB
    @4
    cR
    wbr
    #
    wa
    #
    vz
    wex
    vz
    cA
    cB
    @3
    cR
    cV
    cW
    brcog
    @2
    @7
    @9
    vz
    @1
    @7
    @9
    wb
    @0
    @1
    @6
    @8
    @5
    @4
    cvv
    wcel
    @1
    @6
    @8
    wb
    vz
    vex
    @4
    cB
    cvv
    cW
    cR
    brcnvg
    mpan
    anbi2d
    adantl
    exbidv
    bitrd
end
