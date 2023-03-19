include "cfusgr.mm"
include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "wa.mm"
include "cusgr.mm"
include "cedg.mm"
include "cfn.mm"
include "cnbgr.mm"
include "co.mm"
include "fusgrusgr.mm"
include "adantr.mm"
include "fusgrfis.mm"
include "simpr.mm"
include "eqid.mm"
include "nbusgrfi.mm"
include "syl3anc.mm"

theorem nbfiusgrfi
  let cG: class G
  let cN: class N


  assert |- ( ( G e. FinUSGraph /\ N e. ( Vtx ` G ) ) -> ( G NeighbVtx N ) e. Fin )

  proof
    cG
    cfusgr
    wcel
    #
    cN
    cG
    cvtx
    cfv
    #
    wcel
    #
    wa
    cG
    cusgr
    wcel
    #
    cG
    cedg
    cfv
    #
    cfn
    wcel
    #
    @2
    cG
    cN
    cnbgr
    co
    cfn
    wcel
    @0
    @3
    @2
    cG
    fusgrusgr
    adantr
    @0
    @5
    @2
    cG
    fusgrfis
    adantr
    @0
    @2
    simpr
    cN
    @4
    cG
    @1
    @1
    eqid
    @4
    eqid
    nbusgrfi
    syl3anc
end
