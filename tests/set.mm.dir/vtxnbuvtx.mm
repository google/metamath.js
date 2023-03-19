include "cuvtx.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cnbgr.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "uvtxel.mm"
include "simprbi.mm"

theorem vtxnbuvtx
  let vn: setvar n
  let cG: class G
  let cN: class N
  let cV: class V
  let vv: setvar v
  assume uvtxel.v: |- V = ( Vtx ` G )

  disjoint G n
  disjoint N n
  disjoint V n
  disjoint G v
  disjoint n v
  disjoint N v
  disjoint V v
  assert |- ( N e. ( UnivVtx ` G ) -> A. n e. ( V \ { N } ) n e. ( G NeighbVtx N ) )

  proof
    cN
    cG
    cuvtx
    cfv
    wcel
    cN
    cV
    wcel
    vn
    cv
    cG
    cN
    cnbgr
    co
    wcel
    vn
    cV
    cN
    csn
    cdif
    wral
    vn
    cG
    cN
    cV
    uvtxel.v
    uvtxel
    simprbi
end
