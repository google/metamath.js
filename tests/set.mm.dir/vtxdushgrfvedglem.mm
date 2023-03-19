include "cushgr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "crab.mm"
include "cvv.mm"
include "cmpt.mm"
include "fvex.mm"
include "dmex.mm"
include "rabex.mm"
include "a1i.mm"
include "eqid.mm"
include "eleq2w.mm"
include "cbvrabv.mm"
include "ushgredgedg.mm"
include "hasheqf1od.mm"

theorem vtxdushgrfvedglem
  let cU: class U
  let ve: setvar e
  let vi: setvar i
  let cE: class E
  let cG: class G
  let cV: class V
  let vc: setvar c
  let vx: setvar x
  assume vtxdushgrfvedg.v: |- V = ( Vtx ` G )
  assume vtxdushgrfvedg.e: |- E = ( Edg ` G )

  disjoint E e
  disjoint E i
  disjoint e i
  disjoint G e
  disjoint G i
  disjoint U e
  disjoint U i
  disjoint V e
  disjoint V i
  disjoint E c
  disjoint c e
  disjoint c i
  disjoint G c
  disjoint G x
  disjoint c x
  disjoint e x
  disjoint i x
  disjoint U c
  disjoint U x
  disjoint V c
  disjoint V x
  assert |- ( ( G e. USHGraph /\ U e. V ) -> ( # ` { i e. dom ( iEdg ` G ) | U e. ( ( iEdg ` G ) ` i ) } ) = ( # ` { e e. E | U e. e } ) )

  proof
    cG
    cushgr
    wcel
    cU
    cV
    wcel
    wa
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
    #
    vi
    @1
    cdm
    #
    crab
    #
    cU
    ve
    cv
    wcel
    #
    ve
    cE
    crab
    #
    cvv
    vx
    @4
    vx
    cv
    @1
    cfv
    cmpt
    #
    @4
    cvv
    wcel
    @0
    @2
    vi
    @3
    @1
    cG
    ciedg
    fvex
    dmex
    rabex
    a1i
    vx
    @4
    @6
    vc
    vi
    cE
    @7
    cG
    @1
    cU
    cV
    vtxdushgrfvedg.e
    @1
    eqid
    vtxdushgrfvedg.v
    @4
    eqid
    @5
    cU
    vc
    cv
    wcel
    ve
    vc
    cE
    ve
    vc
    cU
    eleq2w
    cbvrabv
    @7
    eqid
    ushgredgedg
    hasheqf1od
end
