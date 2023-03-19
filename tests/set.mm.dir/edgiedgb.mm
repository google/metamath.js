include "cedg.mm"
include "cfv.mm"
include "wcel.mm"
include "crn.mm"
include "wfun.mm"
include "cv.mm"
include "wceq.mm"
include "cdm.mm"
include "wrex.mm"
include "ciedg.mm"
include "edgval.mm"
include "eqcomi.mm"
include "rneqi.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "elrnrexdmb.mm"
include "syl5bb.mm"

theorem edgiedgb
  let vx: setvar x
  let cE: class E
  let cG: class G
  let cI: class I
  assume edgiedgb.i: |- I = ( iEdg ` G )

  disjoint E x
  disjoint I x
  assert |- ( Fun I -> ( E e. ( Edg ` G ) <-> E. x e. dom I E = ( I ` x ) ) )

  proof
    cE
    cG
    cedg
    cfv
    #
    wcel
    cE
    cI
    crn
    #
    wcel
    cI
    wfun
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
    @0
    @1
    cE
    @0
    cG
    ciedg
    cfv
    #
    crn
    @1
    cG
    edgval
    @2
    cI
    cI
    @2
    edgiedgb.i
    eqcomi
    rneqi
    eqtri
    eleq2i
    vx
    cI
    cE
    elrnrexdmb
    syl5bb
end
