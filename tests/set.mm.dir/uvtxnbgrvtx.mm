include "cuvtx.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cnbgr.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wi.mm"
include "vtxnbuvtx.mm"
include "wa.mm"
include "eleq1w.mm"
include "rspcva.mm"
include "wb.mm"
include "nbgrsym.mm"
include "a1i.mm"
include "syl5ibcom.mm"
include "expcom.mm"
include "com23.mm"
include "mpcom.mm"
include "ralrimiv.mm"

theorem uvtxnbgrvtx
  let vv: setvar v
  let cG: class G
  let cN: class N
  let cV: class V
  let vn: setvar n
  assume uvtxel.v: |- V = ( Vtx ` G )

  disjoint G v
  disjoint N v
  disjoint V v
  disjoint G n
  disjoint n v
  disjoint N n
  disjoint V n
  assert |- ( N e. ( UnivVtx ` G ) -> A. v e. ( V \ { N } ) N e. ( G NeighbVtx v ) )

  proof
    cN
    cG
    cuvtx
    cfv
    wcel
    #
    cN
    cG
    vv
    cv
    #
    cnbgr
    co
    wcel
    #
    vv
    cV
    cN
    csn
    cdif
    #
    vn
    cv
    cG
    cN
    cnbgr
    co
    #
    wcel
    #
    vn
    @3
    wral
    #
    @0
    @1
    @3
    wcel
    #
    @2
    wi
    vn
    cG
    cN
    cV
    uvtxel.v
    vtxnbuvtx
    @6
    @7
    @0
    @2
    @7
    @6
    @0
    @2
    wi
    @7
    @6
    wa
    @1
    @4
    wcel
    #
    @0
    @2
    @5
    @8
    vn
    @1
    @3
    vn
    vv
    @4
    eleq1w
    rspcva
    @8
    @2
    wb
    @0
    cG
    cN
    @1
    nbgrsym
    a1i
    syl5ibcom
    expcom
    com23
    mpcom
    ralrimiv
end
