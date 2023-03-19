include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cpsmet.mm"
include "cbl.mm"
include "cxr.mm"
include "cv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "cmpt2.mm"
include "wceq.mm"
include "xmetpsmet.mm"
include "blfvalps.mm"
include "syl.mm"

theorem blfval
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cX: class X
  let vr: setvar r
  let vd: setvar d

  disjoint r x
  disjoint r y
  disjoint D r
  disjoint x y
  disjoint D x
  disjoint D y
  disjoint X r
  disjoint X x
  disjoint X y
  disjoint d r
  disjoint d x
  disjoint d y
  disjoint D d
  disjoint X d
  assert |- ( D e. ( *Met ` X ) -> ( ball ` D ) = ( x e. X , r e. RR* |-> { y e. X | ( x D y ) < r } ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    cD
    cX
    cpsmet
    cfv
    wcel
    cD
    cbl
    cfv
    vx
    vr
    cX
    cxr
    vx
    cv
    vy
    cv
    cD
    co
    vr
    cv
    clt
    wbr
    vy
    cX
    crab
    cmpt2
    wceq
    cD
    cX
    xmetpsmet
    vx
    vy
    cD
    cX
    vr
    blfvalps
    syl
end
