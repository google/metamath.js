include "cusgr.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "crab.mm"
include "chash.mm"
include "c0.mm"
include "wrex.mm"
include "wn.mm"
include "vtxdusgrfvedg.mm"
include "eqeq1d.mm"
include "cvv.mm"
include "wb.mm"
include "cedg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "hasheq0.mm"
include "mp1i.mm"
include "wral.mm"
include "rabeq0.mm"
include "ralnex.mm"
include "a1i.mm"
include "syl5bb.mm"
include "3bitrd.mm"

theorem vtxdusgr0edgnelALT
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
  assert |- ( ( G e. USGraph /\ U e. V ) -> ( ( D ` U ) = 0 <-> -. E. e e. E U e. e ) )

  proof
    cG
    cusgr
    wcel
    cU
    cV
    wcel
    wa
    #
    cU
    cD
    cfv
    #
    cc0
    wceq
    cU
    ve
    cv
    wcel
    #
    ve
    cE
    crab
    #
    chash
    cfv
    #
    cc0
    wceq
    #
    @3
    c0
    wceq
    #
    @2
    ve
    cE
    wrex
    wn
    #
    @0
    @1
    @4
    cc0
    cD
    cU
    ve
    cE
    cG
    cV
    vtxdushgrfvedg.v
    vtxdushgrfvedg.e
    vtxdushgrfvedg.d
    vtxdusgrfvedg
    eqeq1d
    @3
    cvv
    wcel
    @5
    @6
    wb
    @0
    @2
    ve
    cE
    cE
    cG
    cedg
    cfv
    cvv
    vtxdushgrfvedg.e
    cG
    cedg
    fvex
    eqeltri
    rabex
    @3
    cvv
    hasheq0
    mp1i
    @6
    @2
    wn
    ve
    cE
    wral
    #
    @0
    @7
    @2
    ve
    cE
    rabeq0
    @8
    @7
    wb
    @0
    @2
    ve
    cE
    ralnex
    a1i
    syl5bb
    3bitrd
end
