include "cuhgr.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cdm.mm"
include "wf.mm"
include "w3a.mm"
include "cvtxdg.mm"
include "cc0.mm"
include "wa.mm"
include "cedg.mm"
include "c0.mm"
include "simpl1.mm"
include "simpr.mm"
include "lfuhgr1v0e.mm"
include "adantr.mm"
include "eqid.mm"
include "vtxduhgr0e.mm"
include "syl3anc.mm"
include "ex.mm"

theorem vtxdlfuhgr1v
  let vx: setvar x
  let cU: class U
  let cE: class E
  let cG: class G
  let cI: class I
  let cV: class V
  assume vtxdlfuhgr1v.v: |- V = ( Vtx ` G )
  assume vtxdlfuhgr1v.i: |- I = ( iEdg ` G )
  assume vtxdlfuhgr1v.e: |- E = { x e. ~P V | 2 <_ ( # ` x ) }

  disjoint G x
  disjoint V x
  assert |- ( ( G e. UHGraph /\ ( # ` V ) = 1 /\ I : dom I --> E ) -> ( U e. V -> ( ( VtxDeg ` G ) ` U ) = 0 ) )

  proof
    cG
    cuhgr
    wcel
    #
    cV
    chash
    cfv
    c1
    wceq
    #
    cI
    cdm
    cE
    cI
    wf
    #
    w3a
    #
    cU
    cV
    wcel
    #
    cU
    cG
    cvtxdg
    cfv
    cfv
    cc0
    wceq
    #
    @3
    @4
    wa
    @0
    @4
    cG
    cedg
    cfv
    #
    c0
    wceq
    #
    @5
    @0
    @1
    @2
    @4
    simpl1
    @3
    @4
    simpr
    @3
    @7
    @4
    vx
    cE
    cG
    cI
    cV
    vtxdlfuhgr1v.v
    vtxdlfuhgr1v.i
    vtxdlfuhgr1v.e
    lfuhgr1v0e
    adantr
    cU
    @6
    cG
    cV
    vtxdlfuhgr1v.v
    @6
    eqid
    vtxduhgr0e
    syl3anc
    ex
end
