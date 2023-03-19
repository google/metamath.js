include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cbl.mm"
include "crn.mm"
include "ctg.mm"
include "cuni.mm"
include "wss.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "mopnval.mm"
include "eleq2d.mm"
include "ctb.mm"
include "wb.mm"
include "blbas.mm"
include "eltg2.mm"
include "syl.mm"
include "unirnbl.mm"
include "sseq2d.mm"
include "anbi1d.mm"
include "3bitrd.mm"

theorem elmopn
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cJ: class J
  let cX: class X
  let vz: setvar z
  let vd: setvar d
  assume mopnval.1: |- J = ( MetOpen ` D )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint D x
  disjoint D y
  disjoint X x
  disjoint X y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint D d
  disjoint D z
  disjoint X z
  assert |- ( D e. ( *Met ` X ) -> ( A e. J <-> ( A C_ X /\ A. x e. A E. y e. ran ( ball ` D ) ( x e. y /\ y C_ A ) ) ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cA
    cJ
    wcel
    cA
    cD
    cbl
    cfv
    crn
    #
    ctg
    cfv
    #
    wcel
    #
    cA
    @1
    cuni
    #
    wss
    #
    vx
    cv
    vy
    cv
    #
    wcel
    @6
    cA
    wss
    wa
    vy
    @1
    wrex
    vx
    cA
    wral
    #
    wa
    #
    cA
    cX
    wss
    #
    @7
    wa
    @0
    cJ
    @2
    cA
    cD
    cJ
    cX
    mopnval.1
    mopnval
    eleq2d
    @0
    @1
    ctb
    wcel
    @3
    @8
    wb
    cD
    cX
    blbas
    vx
    vy
    cA
    @1
    ctb
    eltg2
    syl
    @0
    @5
    @9
    @7
    @0
    @4
    cX
    cA
    cD
    cX
    unirnbl
    sseq2d
    anbi1d
    3bitrd
end
