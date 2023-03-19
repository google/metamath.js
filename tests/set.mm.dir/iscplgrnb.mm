include "wcel.mm"
include "ccplgr.mm"
include "cv.mm"
include "cuvtx.mm"
include "cfv.mm"
include "wral.mm"
include "cnbgr.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "iscplgr.mm"
include "wa.mm"
include "wb.mm"
include "uvtxel.mm"
include "a1i.mm"
include "baibd.mm"
include "ralbidva.mm"
include "bitrd.mm"

theorem iscplgrnb
  let vv: setvar v
  let vn: setvar n
  let cG: class G
  let cV: class V
  let cW: class W
  let vg: setvar g
  assume cplgruvtxb.v: |- V = ( Vtx ` G )

  disjoint G v
  disjoint V v
  disjoint G n
  disjoint n v
  disjoint V n
  disjoint W v
  disjoint G g
  disjoint V g
  disjoint g v
  disjoint W g
  assert |- ( G e. W -> ( G e. ComplGraph <-> A. v e. V A. n e. ( V \ { v } ) n e. ( G NeighbVtx v ) ) )

  proof
    cG
    cW
    wcel
    #
    cG
    ccplgr
    wcel
    vv
    cv
    #
    cG
    cuvtx
    cfv
    wcel
    #
    vv
    cV
    wral
    vn
    cv
    cG
    @1
    cnbgr
    co
    wcel
    vn
    cV
    @1
    csn
    cdif
    wral
    #
    vv
    cV
    wral
    vv
    cG
    cV
    cW
    cplgruvtxb.v
    iscplgr
    @0
    @2
    @3
    vv
    cV
    @0
    @2
    @1
    cV
    wcel
    #
    @3
    @2
    @4
    @3
    wa
    wb
    @0
    vn
    cG
    @1
    cV
    cplgruvtxb.v
    uvtxel
    a1i
    baibd
    ralbidva
    bitrd
end
