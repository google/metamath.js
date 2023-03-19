include "cushgr.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cvtxdg.mm"
include "cv.mm"
include "ciedg.mm"
include "cdm.mm"
include "crab.mm"
include "chash.mm"
include "csn.mm"
include "wceq.mm"
include "cxad.mm"
include "co.mm"
include "fveq1i.mm"
include "a1i.mm"
include "eqid.mm"
include "vtxdgval.mm"
include "adantl.mm"
include "vtxdushgrfvedglem.mm"
include "cvv.mm"
include "cmpt.mm"
include "fvex.mm"
include "dmex.mm"
include "rabex.mm"
include "eqeq1.mm"
include "cbvrabv.mm"
include "ushgredgedgloop.mm"
include "hasheqf1od.mm"
include "oveq12d.mm"
include "3eqtrd.mm"

theorem vtxdushgrfvedg
  let cD: class D
  let cU: class U
  let ve: setvar e
  let cE: class E
  let cG: class G
  let cV: class V
  let vc: setvar c
  let vi: setvar i
  let vx: setvar x
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
  assert |- ( ( G e. USHGraph /\ U e. V ) -> ( D ` U ) = ( ( # ` { e e. E | U e. e } ) +e ( # ` { e e. E | e = { U } } ) ) )

  proof
    cG
    cushgr
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
    #
    cU
    cG
    cvtxdg
    cfv
    #
    cfv
    #
    cU
    vi
    cv
    cG
    ciedg
    cfv
    #
    cfv
    #
    wcel
    vi
    @6
    cdm
    #
    crab
    chash
    cfv
    #
    @7
    cU
    csn
    #
    wceq
    #
    vi
    @8
    crab
    #
    chash
    cfv
    #
    cxad
    co
    #
    cU
    ve
    cv
    #
    wcel
    ve
    cE
    crab
    chash
    cfv
    #
    @15
    @10
    wceq
    #
    ve
    cE
    crab
    #
    chash
    cfv
    #
    cxad
    co
    @3
    @5
    wceq
    @2
    cU
    cD
    @4
    vtxdushgrfvedg.d
    fveq1i
    a1i
    @1
    @5
    @14
    wceq
    @0
    vi
    @8
    cU
    cG
    @6
    cV
    vtxdushgrfvedg.v
    @6
    eqid
    #
    @8
    eqid
    vtxdgval
    adantl
    @2
    @9
    @16
    @13
    @19
    cxad
    cU
    ve
    vi
    cE
    cG
    cV
    vtxdushgrfvedg.v
    vtxdushgrfvedg.e
    vtxdushgrfvedglem
    @2
    @12
    @18
    cvv
    vx
    @12
    vx
    cv
    @6
    cfv
    cmpt
    #
    @12
    cvv
    wcel
    @2
    @11
    vi
    @8
    @6
    cG
    ciedg
    fvex
    dmex
    rabex
    a1i
    vx
    @12
    @18
    vc
    vi
    cE
    @21
    cG
    @6
    cU
    cV
    vtxdushgrfvedg.e
    @20
    vtxdushgrfvedg.v
    @12
    eqid
    @17
    vc
    cv
    #
    @10
    wceq
    ve
    vc
    cE
    @15
    @22
    @10
    eqeq1
    cbvrabv
    @21
    eqid
    ushgredgedgloop
    hasheqf1od
    oveq12d
    3eqtrd
end
