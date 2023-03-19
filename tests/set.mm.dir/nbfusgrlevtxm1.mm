include "cfusgr.mm"
include "wcel.mm"
include "wa.mm"
include "cnbgr.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "c1.mm"
include "cmin.mm"
include "cle.mm"
include "cvv.mm"
include "wss.mm"
include "wbr.mm"
include "cvtx.mm"
include "fvexi.mm"
include "difexi.mm"
include "nbgrssovtx.mm"
include "a1i.mm"
include "hashss.mm"
include "sylancr.mm"
include "cfn.mm"
include "wceq.mm"
include "fusgrvtxfi.mm"
include "hashdifsn.mm"
include "eqcomd.mm"
include "sylan.mm"
include "breqtrrd.mm"

theorem nbfusgrlevtxm1
  let cU: class U
  let cG: class G
  let cV: class V
  assume hashnbusgrnn0.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. FinUSGraph /\ U e. V ) -> ( # ` ( G NeighbVtx U ) ) <_ ( ( # ` V ) - 1 ) )

  proof
    cG
    cfusgr
    wcel
    #
    cU
    cV
    wcel
    #
    wa
    #
    cG
    cU
    cnbgr
    co
    #
    chash
    cfv
    #
    cV
    cU
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
    c1
    cmin
    co
    #
    cle
    @2
    @6
    cvv
    wcel
    @3
    @6
    wss
    #
    @4
    @7
    cle
    wbr
    cV
    @5
    cV
    cG
    cvtx
    hashnbusgrnn0.v
    fvexi
    difexi
    @9
    @2
    cG
    cV
    cU
    hashnbusgrnn0.v
    nbgrssovtx
    a1i
    @6
    @3
    cvv
    hashss
    sylancr
    @0
    cV
    cfn
    wcel
    #
    @1
    @8
    @7
    wceq
    cG
    cV
    hashnbusgrnn0.v
    fusgrvtxfi
    @10
    @1
    wa
    @7
    @8
    cV
    cU
    hashdifsn
    eqcomd
    sylan
    breqtrrd
end
