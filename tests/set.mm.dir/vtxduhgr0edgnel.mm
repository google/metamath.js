include "cuhgr.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "ciedg.mm"
include "cdm.mm"
include "wrex.mm"
include "wn.mm"
include "wb.mm"
include "eqid.mm"
include "vtxd0nedgb.mm"
include "adantl.mm"
include "uhgrvtxedgiedgb.mm"
include "notbid.mm"
include "bitrd.mm"

theorem vtxduhgr0edgnel
  let cD: class D
  let cU: class U
  let ve: setvar e
  let cE: class E
  let cG: class G
  let cV: class V
  let vc: setvar c
  let vi: setvar i
  let vx: setvar x
  let vv: setvar v
  assume vtxdushgrfvedg.v: |- V = ( Vtx ` G )
  assume vtxdushgrfvedg.e: |- E = ( Edg ` G )
  assume vtxdushgrfvedg.d: |- D = ( VtxDeg ` G )

  disjoint E e
  disjoint G e
  disjoint U e
  disjoint V e
  disjoint E c
  disjoint E i
  disjoint c e
  disjoint c i
  disjoint e i
  disjoint G c
  disjoint G i
  disjoint G x
  disjoint c x
  disjoint e x
  disjoint i x
  disjoint U c
  disjoint U i
  disjoint U x
  disjoint V c
  disjoint V i
  disjoint V x
  disjoint G v
  disjoint i v
  disjoint U v
  disjoint V v
  assert |- ( ( G e. UHGraph /\ U e. V ) -> ( ( D ` U ) = 0 <-> -. E. e e. E U e. e ) )

  proof
    cG
    cuhgr
    wcel
    #
    cU
    cV
    wcel
    #
    wa
    #
    cU
    cD
    cfv
    cc0
    wceq
    #
    cU
    vi
    cv
    cG
    ciedg
    cfv
    #
    cfv
    wcel
    vi
    @4
    cdm
    wrex
    #
    wn
    #
    cU
    ve
    cv
    wcel
    ve
    cE
    wrex
    #
    wn
    @1
    @3
    @6
    wb
    @0
    cD
    cU
    vi
    cG
    @4
    cV
    vtxdushgrfvedg.v
    @4
    eqid
    #
    vtxdushgrfvedg.d
    vtxd0nedgb
    adantl
    @2
    @5
    @7
    cU
    ve
    vi
    cE
    cG
    @4
    cV
    vtxdushgrfvedg.v
    @8
    vtxdushgrfvedg.e
    uhgrvtxedgiedgb
    notbid
    bitrd
end
