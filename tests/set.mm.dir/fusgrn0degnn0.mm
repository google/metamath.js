include "c0.mm"
include "wne.mm"
include "cfusgr.mm"
include "wcel.mm"
include "cv.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "wceq.mm"
include "cn0.mm"
include "wrex.mm"
include "wex.mm"
include "wi.mm"
include "n0.mm"
include "wral.mm"
include "vtxdgfusgr.mm"
include "weq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "risset.mm"
include "eqeq1d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "rexbidv.mm"
include "rspcev.mm"
include "expcom.mm"
include "sylbi.mm"
include "com12.mm"
include "syld.mm"
include "syl5.mm"
include "exlimiv.mm"
include "impcom.mm"

theorem fusgrn0degnn0
  let vv: setvar v
  let vn: setvar n
  let cG: class G
  let cV: class V
  let vk: setvar k
  let vu: setvar u
  assume fusgrn0degnn0.v: |- V = ( Vtx ` G )

  disjoint G n
  disjoint G v
  disjoint n v
  disjoint V v
  disjoint G k
  disjoint G u
  disjoint k n
  disjoint k u
  disjoint k v
  disjoint n u
  disjoint u v
  disjoint V k
  disjoint V u
  assert |- ( ( G e. FinUSGraph /\ V =/= (/) ) -> E. v e. V E. n e. NN0 ( ( VtxDeg ` G ) ` v ) = n )

  proof
    cV
    c0
    wne
    #
    cG
    cfusgr
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
    vn
    cv
    #
    wceq
    #
    vn
    cn0
    wrex
    #
    vv
    cV
    wrex
    #
    @0
    vk
    cv
    #
    cV
    wcel
    #
    vk
    wex
    @1
    @8
    wi
    #
    vk
    cV
    n0
    @10
    @11
    vk
    @1
    vu
    cv
    #
    @3
    cfv
    #
    cn0
    wcel
    #
    vu
    cV
    wral
    #
    @10
    @8
    vu
    cG
    cV
    fusgrn0degnn0.v
    vtxdgfusgr
    @10
    @15
    @9
    @3
    cfv
    #
    cn0
    wcel
    #
    @8
    @14
    @17
    vu
    @9
    cV
    vu
    vk
    weq
    @13
    @16
    cn0
    @12
    @9
    @3
    fveq2
    eleq1d
    rspcv
    @17
    @10
    @8
    @17
    @5
    @16
    wceq
    #
    vn
    cn0
    wrex
    #
    @10
    @8
    wi
    vn
    @16
    cn0
    risset
    @10
    @19
    @8
    @7
    @19
    vv
    @9
    cV
    vv
    vk
    weq
    #
    @6
    @18
    vn
    cn0
    @20
    @6
    @16
    @5
    wceq
    @18
    @20
    @4
    @16
    @5
    @2
    @9
    @3
    fveq2
    eqeq1d
    @16
    @5
    eqcom
    syl6bb
    rexbidv
    rspcev
    expcom
    sylbi
    com12
    syld
    syl5
    exlimiv
    sylbi
    impcom
end
