include "wcel.mm"
include "cuvtx.mm"
include "cfv.mm"
include "cnbgr.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "wceq.mm"
include "uvtxnbgr.mm"
include "wa.mm"
include "cv.mm"
include "wral.mm"
include "simpl.mm"
include "raleleq.mm"
include "eqcoms.mm"
include "adantl.mm"
include "uvtxel.mm"
include "sylanbrc.mm"
include "ex.mm"
include "impbid2.mm"

theorem uvtxnbgrb
  let cG: class G
  let cN: class N
  let cV: class V
  let vn: setvar n
  assume uvtxnbgr.v: |- V = ( Vtx ` G )


  assert |- ( N e. V -> ( N e. ( UnivVtx ` G ) <-> ( G NeighbVtx N ) = ( V \ { N } ) ) )

  proof
    cN
    cV
    wcel
    #
    cN
    cG
    cuvtx
    cfv
    wcel
    #
    cG
    cN
    cnbgr
    co
    #
    cV
    cN
    csn
    cdif
    #
    wceq
    #
    cG
    cN
    cV
    uvtxnbgr.v
    uvtxnbgr
    @0
    @4
    @1
    @0
    @4
    wa
    @0
    vn
    cv
    @2
    wcel
    vn
    @3
    wral
    #
    @1
    @0
    @4
    simpl
    @4
    @5
    @0
    @5
    @3
    @2
    vn
    @3
    @2
    raleleq
    eqcoms
    adantl
    vn
    cG
    cN
    cV
    uvtxnbgr.v
    uvtxel
    sylanbrc
    ex
    impbid2
end
