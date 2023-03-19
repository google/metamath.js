include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "ccom.mm"
include "wss.mm"
include "ccnv.mm"
include "wceq.mm"
include "wrex.mm"
include "simplll.mm"
include "simplr.mm"
include "ustexsym.mm"
include "syl2anc.mm"
include "simprl.mm"
include "coss1.mm"
include "coss2.mm"
include "sstrd.mm"
include "ad2antll.mm"
include "simpllr.mm"
include "jca.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "ustexhalf.mm"
include "r19.29a.mm"

theorem ustex2sym
  let vw: setvar w
  let cU: class U
  let cV: class V
  let cX: class X
  let vv: setvar v

  disjoint U w
  disjoint V w
  disjoint X w
  disjoint v w
  disjoint U v
  disjoint V v
  disjoint X v
  assert |- ( ( U e. ( UnifOn ` X ) /\ V e. U ) -> E. w e. U ( `' w = w /\ ( w o. w ) C_ V ) )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    cV
    cU
    wcel
    #
    wa
    #
    vv
    cv
    #
    @3
    ccom
    #
    cV
    wss
    #
    vw
    cv
    #
    ccnv
    @6
    wceq
    #
    @6
    @6
    ccom
    #
    cV
    wss
    #
    wa
    #
    vw
    cU
    wrex
    #
    vv
    cU
    @2
    @3
    cU
    wcel
    #
    wa
    #
    @5
    wa
    #
    @7
    @6
    @3
    wss
    #
    wa
    #
    vw
    cU
    wrex
    #
    @11
    @14
    @0
    @12
    @17
    @0
    @1
    @12
    @5
    simplll
    @2
    @12
    @5
    simplr
    vw
    cU
    @3
    cX
    ustexsym
    syl2anc
    @14
    @16
    @10
    vw
    cU
    @14
    @6
    cU
    wcel
    #
    wa
    #
    @16
    @10
    @19
    @16
    wa
    #
    @7
    @9
    @19
    @7
    @15
    simprl
    @20
    @8
    @4
    cV
    @15
    @8
    @4
    wss
    @19
    @7
    @15
    @8
    @3
    @6
    ccom
    @4
    @6
    @3
    @6
    coss1
    @6
    @3
    @3
    coss2
    sstrd
    ad2antll
    @13
    @5
    @18
    @16
    simpllr
    sstrd
    jca
    ex
    reximdva
    mpd
    vv
    cU
    cV
    cX
    ustexhalf
    r19.29a
end
