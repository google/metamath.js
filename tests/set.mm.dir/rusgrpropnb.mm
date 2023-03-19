include "crusgr.mm"
include "wbr.mm"
include "cusgr.mm"
include "wcel.mm"
include "cxnn0.mm"
include "cv.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "cnbgr.mm"
include "co.mm"
include "chash.mm"
include "eqid.mm"
include "rusgrprop0.mm"
include "simp1.mm"
include "simp2.mm"
include "wa.mm"
include "hashnbusgrvd.mm"
include "adantlr.mm"
include "wb.mm"
include "eqeq2.mm"
include "eqcoms.mm"
include "syl5ibrcom.mm"
include "ralimdva.mm"
include "3impia.mm"
include "3jca.mm"
include "syl.mm"

theorem rusgrpropnb
  let vv: setvar v
  let cG: class G
  let cK: class K
  let cV: class V
  assume rusgrpropnb.v: |- V = ( Vtx ` G )

  disjoint G v
  disjoint K v
  assert |- ( G RegUSGraph K -> ( G e. USGraph /\ K e. NN0* /\ A. v e. V ( # ` ( G NeighbVtx v ) ) = K ) )

  proof
    cG
    cK
    crusgr
    wbr
    cG
    cusgr
    wcel
    #
    cK
    cxnn0
    wcel
    #
    vv
    cv
    #
    cG
    cvtxdg
    cfv
    #
    cfv
    #
    cK
    wceq
    #
    vv
    cV
    wral
    #
    w3a
    #
    @0
    @1
    cG
    @2
    cnbgr
    co
    chash
    cfv
    #
    cK
    wceq
    #
    vv
    cV
    wral
    #
    w3a
    vv
    @3
    cG
    cK
    cV
    rusgrpropnb.v
    @3
    eqid
    rusgrprop0
    @7
    @0
    @1
    @10
    @0
    @1
    @6
    simp1
    @0
    @1
    @6
    simp2
    @0
    @1
    @6
    @10
    @0
    @1
    wa
    #
    @5
    @9
    vv
    cV
    @11
    @2
    cV
    wcel
    #
    wa
    @9
    @5
    @8
    @4
    wceq
    #
    @0
    @12
    @13
    @1
    @2
    cG
    cV
    rusgrpropnb.v
    hashnbusgrvd
    adantlr
    @9
    @13
    wb
    cK
    @4
    cK
    @4
    @8
    eqeq2
    eqcoms
    syl5ibrcom
    ralimdva
    3impia
    3jca
    syl
end
