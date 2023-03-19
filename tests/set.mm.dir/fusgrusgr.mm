include "cfusgr.mm"
include "wcel.mm"
include "cusgr.mm"
include "cvtx.mm"
include "cfv.mm"
include "cfn.mm"
include "eqid.mm"
include "isfusgr.mm"
include "simplbi.mm"

theorem fusgrusgr
  let cG: class G


  assert |- ( G e. FinUSGraph -> G e. USGraph )

  proof
    cG
    cfusgr
    wcel
    cG
    cusgr
    wcel
    cG
    cvtx
    cfv
    #
    cfn
    wcel
    cG
    @0
    @0
    eqid
    isfusgr
    simplbi
end
