include "crusgr.mm"
include "wbr.mm"
include "cusgr.mm"
include "wcel.mm"
include "cxnn0.mm"
include "cv.mm"
include "cnbgr.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "cpr.mm"
include "cedg.mm"
include "crab.mm"
include "rusgrpropnb.mm"
include "simp1.mm"
include "simp2.mm"
include "wa.mm"
include "eqid.mm"
include "nbusgrvtx.mm"
include "fveq2d.mm"
include "eqcomd.mm"
include "adantr.mm"
include "simpr.mm"
include "eqtrd.mm"
include "ex.mm"
include "ralimdva.mm"
include "imp.mm"
include "3adant2.mm"
include "3jca.mm"
include "syl.mm"

theorem rusgrpropadjvtx
  let vv: setvar v
  let vk: setvar k
  let cG: class G
  let cK: class K
  let cV: class V
  let ve: setvar e
  assume rusgrpropnb.v: |- V = ( Vtx ` G )

  disjoint G v
  disjoint K v
  disjoint G k
  disjoint k v
  disjoint V k
  disjoint G e
  disjoint e v
  assert |- ( G RegUSGraph K -> ( G e. USGraph /\ K e. NN0* /\ A. v e. V ( # ` { k e. V | { v , k } e. ( Edg ` G ) } ) = K ) )

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
    cG
    vv
    cv
    #
    cnbgr
    co
    #
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
    #
    @0
    @1
    @2
    vk
    cv
    cpr
    cG
    cedg
    cfv
    #
    wcel
    vk
    cV
    crab
    #
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
    cG
    cK
    cV
    rusgrpropnb.v
    rusgrpropnb
    @7
    @0
    @1
    @12
    @0
    @1
    @6
    simp1
    @0
    @1
    @6
    simp2
    @0
    @6
    @12
    @1
    @0
    @6
    @12
    @0
    @5
    @11
    vv
    cV
    @0
    @2
    cV
    wcel
    wa
    #
    @5
    @11
    @13
    @5
    wa
    @10
    @4
    cK
    @13
    @10
    @4
    wceq
    @5
    @13
    @4
    @10
    @13
    @3
    @9
    chash
    vk
    @8
    cG
    @2
    cV
    rusgrpropnb.v
    @8
    eqid
    nbusgrvtx
    fveq2d
    eqcomd
    adantr
    @13
    @5
    simpr
    eqtrd
    ex
    ralimdva
    imp
    3adant2
    3jca
    syl
end
