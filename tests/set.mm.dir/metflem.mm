include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "cr.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "cdm.mm"
include "elfvdm.mm"
include "ismet.mm"
include "syl.mm"
include "ibi.mm"

theorem metflem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let cX: class X
  let cA: class A
  let cB: class B
  let vd: setvar d
  let vw: setvar w
  let cR: class R
  let cC: class C

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint D d
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint D w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint C z
  assert |- ( D e. ( Met ` X ) -> ( D : ( X X. X ) --> RR /\ A. x e. X A. y e. X ( ( ( x D y ) = 0 <-> x = y ) /\ A. z e. X ( x D y ) <_ ( ( z D x ) + ( z D y ) ) ) ) )

  proof
    cD
    cX
    cme
    cfv
    wcel
    #
    cX
    cX
    cxp
    cr
    cD
    wf
    vx
    cv
    #
    vy
    cv
    #
    cD
    co
    #
    cc0
    wceq
    @1
    @2
    wceq
    wb
    @3
    vz
    cv
    #
    @1
    cD
    co
    @4
    @2
    cD
    co
    caddc
    co
    cle
    wbr
    vz
    cX
    wral
    wa
    vy
    cX
    wral
    vx
    cX
    wral
    wa
    #
    @0
    cX
    cme
    cdm
    #
    wcel
    @0
    @5
    wb
    cD
    cX
    cme
    elfvdm
    vx
    vy
    vz
    @6
    cD
    cX
    ismet
    syl
    ibi
end
