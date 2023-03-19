include "ccplgr.mm"
include "wcel.mm"
include "wa.mm"
include "cuvtx.mm"
include "cfv.mm"
include "cnbgr.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "wceq.mm"
include "cplgruvtxb.mm"
include "ibi.mm"
include "eqcomd.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "wb.mm"
include "uvtxnbgrb.mm"
include "adantl.mm"
include "mpbid.mm"

theorem nbcplgr
  let cG: class G
  let cN: class N
  let cV: class V
  assume nbcplgr.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. ComplGraph /\ N e. V ) -> ( G NeighbVtx N ) = ( V \ { N } ) )

  proof
    cG
    ccplgr
    wcel
    #
    cN
    cV
    wcel
    #
    wa
    cN
    cG
    cuvtx
    cfv
    #
    wcel
    #
    cG
    cN
    cnbgr
    co
    cV
    cN
    csn
    cdif
    wceq
    #
    @0
    @1
    @3
    @0
    cV
    @2
    cN
    @0
    @2
    cV
    @0
    @2
    cV
    wceq
    cG
    cV
    ccplgr
    nbcplgr.v
    cplgruvtxb
    ibi
    eqcomd
    eleq2d
    biimpa
    @1
    @3
    @4
    wb
    @0
    cG
    cN
    cV
    nbcplgr.v
    uvtxnbgrb
    adantl
    mpbid
end
