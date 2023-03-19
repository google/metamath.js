include "cuhgr.mm"
include "wcel.mm"
include "wfun.mm"
include "cedg.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "cdm.mm"
include "wrex.mm"
include "wb.mm"
include "uhgrfun.mm"
include "edgiedgb.mm"
include "syl.mm"

theorem uhgredgiedgb
  let vx: setvar x
  let cE: class E
  let cG: class G
  let cI: class I
  assume uhgredgiedgb.i: |- I = ( iEdg ` G )

  disjoint E x
  disjoint I x
  assert |- ( G e. UHGraph -> ( E e. ( Edg ` G ) <-> E. x e. dom I E = ( I ` x ) ) )

  proof
    cG
    cuhgr
    wcel
    cI
    wfun
    cE
    cG
    cedg
    cfv
    wcel
    cE
    vx
    cv
    cI
    cfv
    wceq
    vx
    cI
    cdm
    wrex
    wb
    cI
    cG
    uhgredgiedgb.i
    uhgrfun
    vx
    cE
    cG
    cI
    uhgredgiedgb.i
    edgiedgb
    syl
end
