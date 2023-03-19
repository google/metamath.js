include "cuhgr.mm"
include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "cpr.mm"
include "wrex.mm"
include "wn.mm"
include "wa.mm"
include "ciedg.mm"
include "cdm.mm"
include "wb.mm"
include "eqid.mm"
include "vtxd0nedgb.mm"
include "adantl.mm"
include "cedg.mm"
include "eleq2i.mm"
include "uhgredgiedgb.mm"
include "syl5bb.mm"
include "adantr.mm"
include "wi.mm"
include "prid1g.mm"
include "eleq2.mm"
include "syl5ibcom.mm"
include "reximdv.mm"
include "sylbid.mm"
include "rexlimdvw.mm"
include "con3d.mm"
include "3impia.mm"

theorem vtxduhgr0nedg
  let vv: setvar v
  let cD: class D
  let cU: class U
  let cE: class E
  let cG: class G
  let cV: class V
  let vc: setvar c
  let ve: setvar e
  let vi: setvar i
  let vx: setvar x
  assume vtxdushgrfvedg.v: |- V = ( Vtx ` G )
  assume vtxdushgrfvedg.e: |- E = ( Edg ` G )
  assume vtxdushgrfvedg.d: |- D = ( VtxDeg ` G )

  disjoint G v
  disjoint U v
  disjoint V v
  disjoint E c
  disjoint E e
  disjoint E i
  disjoint c e
  disjoint c i
  disjoint e i
  disjoint G c
  disjoint G e
  disjoint G i
  disjoint G x
  disjoint c x
  disjoint e x
  disjoint i x
  disjoint U c
  disjoint U e
  disjoint U i
  disjoint U x
  disjoint V c
  disjoint V e
  disjoint V i
  disjoint V x
  disjoint i v
  assert |- ( ( G e. UHGraph /\ U e. V /\ ( D ` U ) = 0 ) -> -. E. v e. V { U , v } e. E )

  proof
    cG
    cuhgr
    wcel
    #
    cU
    cV
    wcel
    #
    cU
    cD
    cfv
    cc0
    wceq
    #
    cU
    vv
    cv
    #
    cpr
    #
    cE
    wcel
    #
    vv
    cV
    wrex
    #
    wn
    #
    @0
    @1
    wa
    #
    @2
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
    #
    vi
    @9
    cdm
    #
    wrex
    #
    wn
    #
    @7
    @1
    @2
    @14
    wb
    @0
    cD
    cU
    vi
    cG
    @9
    cV
    vtxdushgrfvedg.v
    @9
    eqid
    #
    vtxdushgrfvedg.d
    vtxd0nedgb
    adantl
    @8
    @6
    @13
    @8
    @5
    @13
    vv
    cV
    @8
    @5
    @4
    @10
    wceq
    #
    vi
    @12
    wrex
    #
    @13
    @0
    @5
    @17
    wb
    @1
    @5
    @4
    cG
    cedg
    cfv
    #
    wcel
    @0
    @17
    cE
    @18
    @4
    vtxdushgrfvedg.e
    eleq2i
    vi
    @4
    cG
    @9
    @15
    uhgredgiedgb
    syl5bb
    adantr
    @8
    @16
    @11
    vi
    @12
    @1
    @16
    @11
    wi
    @0
    @1
    cU
    @4
    wcel
    @16
    @11
    cU
    @3
    cV
    prid1g
    @4
    @10
    cU
    eleq2
    syl5ibcom
    adantl
    reximdv
    sylbid
    rexlimdvw
    con3d
    sylbid
    3impia
end
