include "cfusgr.mm"
include "wcel.mm"
include "wa.mm"
include "cnbgr.mm"
include "co.mm"
include "cfn.mm"
include "chash.mm"
include "cfv.mm"
include "cn0.mm"
include "cvtx.mm"
include "eleq2i.mm"
include "nbfiusgrfi.mm"
include "sylan2b.mm"
include "hashcl.mm"
include "syl.mm"

theorem hashnbusgrnn0
  let cU: class U
  let cG: class G
  let cV: class V
  assume hashnbusgrnn0.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. FinUSGraph /\ U e. V ) -> ( # ` ( G NeighbVtx U ) ) e. NN0 )

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
    cG
    cU
    cnbgr
    co
    #
    cfn
    wcel
    #
    @2
    chash
    cfv
    cn0
    wcel
    @1
    @0
    cU
    cG
    cvtx
    cfv
    #
    wcel
    @3
    cV
    @4
    cU
    hashnbusgrnn0.v
    eleq2i
    cG
    cU
    nbfiusgrfi
    sylan2b
    @2
    hashcl
    syl
end
