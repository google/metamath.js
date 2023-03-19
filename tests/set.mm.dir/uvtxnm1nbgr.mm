include "cfusgr.mm"
include "wcel.mm"
include "cuvtx.mm"
include "cfv.mm"
include "wa.mm"
include "cnbgr.mm"
include "co.mm"
include "chash.mm"
include "csn.mm"
include "cdif.mm"
include "cmin.mm"
include "c1.mm"
include "wceq.mm"
include "uvtxnbgr.mm"
include "adantl.mm"
include "fveq2d.mm"
include "cfn.mm"
include "wss.mm"
include "fusgrvtxfi.mm"
include "uvtxisvtx.mm"
include "snssd.mm"
include "hashssdif.mm"
include "syl2an.mm"
include "hashsng.mm"
include "oveq2d.mm"
include "3eqtrd.mm"

theorem uvtxnm1nbgr
  let cG: class G
  let cN: class N
  let cV: class V
  assume uvtxnm1nbgr.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. FinUSGraph /\ N e. ( UnivVtx ` G ) ) -> ( # ` ( G NeighbVtx N ) ) = ( ( # ` V ) - 1 ) )

  proof
    cG
    cfusgr
    wcel
    #
    cN
    cG
    cuvtx
    cfv
    #
    wcel
    #
    wa
    #
    cG
    cN
    cnbgr
    co
    #
    chash
    cfv
    cV
    cN
    csn
    #
    cdif
    #
    chash
    cfv
    #
    cV
    chash
    cfv
    #
    @5
    chash
    cfv
    #
    cmin
    co
    #
    @8
    c1
    cmin
    co
    @3
    @4
    @6
    chash
    @2
    @4
    @6
    wceq
    @0
    cG
    cN
    cV
    uvtxnm1nbgr.v
    uvtxnbgr
    adantl
    fveq2d
    @0
    cV
    cfn
    wcel
    @5
    cV
    wss
    @7
    @10
    wceq
    @2
    cG
    cV
    uvtxnm1nbgr.v
    fusgrvtxfi
    @2
    cN
    cV
    cG
    cN
    cV
    uvtxnm1nbgr.v
    uvtxisvtx
    snssd
    cV
    @5
    hashssdif
    syl2an
    @3
    @9
    c1
    @8
    cmin
    @2
    @9
    c1
    wceq
    @0
    cN
    @1
    hashsng
    adantl
    oveq2d
    3eqtrd
end
