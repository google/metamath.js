include "cuhgr.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "cc0.mm"
include "wa.mm"
include "ciedg.mm"
include "wb.mm"
include "wfun.mm"
include "eqid.mm"
include "uhgrfun.mm"
include "edg0iedg0.mm"
include "syl.mm"
include "adantr.mm"
include "wi.mm"
include "vtxdg0e.mm"
include "ex.mm"
include "adantl.mm"
include "sylbid.mm"
include "3impia.mm"

theorem vtxduhgr0e
  let cU: class U
  let cE: class E
  let cG: class G
  let cV: class V
  assume vtxduhgr0e.v: |- V = ( Vtx ` G )
  assume vtxduhgr0e.e: |- E = ( Edg ` G )


  assert |- ( ( G e. UHGraph /\ U e. V /\ E = (/) ) -> ( ( VtxDeg ` G ) ` U ) = 0 )

  proof
    cG
    cuhgr
    wcel
    #
    cU
    cV
    wcel
    #
    cE
    c0
    wceq
    #
    cU
    cG
    cvtxdg
    cfv
    cfv
    cc0
    wceq
    #
    @0
    @1
    wa
    @2
    cG
    ciedg
    cfv
    #
    c0
    wceq
    #
    @3
    @0
    @2
    @5
    wb
    #
    @1
    @0
    @4
    wfun
    @6
    @4
    cG
    @4
    eqid
    #
    uhgrfun
    cE
    cG
    @4
    @7
    vtxduhgr0e.e
    edg0iedg0
    syl
    adantr
    @1
    @5
    @3
    wi
    @0
    @1
    @5
    @3
    cU
    cG
    @4
    cV
    vtxduhgr0e.v
    @7
    vtxdg0e
    ex
    adantl
    sylbid
    3impia
end
