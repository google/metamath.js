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
include "ustex2sym.mm"
include "syl2anc.mm"
include "simprl.mm"
include "simp-5l.mm"
include "ustssco.mm"
include "simprr.mm"
include "coss2.mm"
include "adantl.mm"
include "sstr.mm"
include "coss1.mm"
include "syl.mm"
include "sstrd.mm"
include "simpllr.mm"
include "jca.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "ustexhalf.mm"
include "r19.29a.mm"

theorem ustex3sym
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
  assert |- ( ( U e. ( UnifOn ` X ) /\ V e. U ) -> E. w e. U ( `' w = w /\ ( w o. ( w o. w ) ) C_ V ) )

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
    @6
    ccom
    #
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
    @8
    @3
    wss
    #
    wa
    #
    vw
    cU
    wrex
    #
    @12
    @15
    @0
    @13
    @18
    @0
    @1
    @13
    @5
    simplll
    @2
    @13
    @5
    simplr
    vw
    cU
    @3
    cX
    ustex2sym
    syl2anc
    @15
    @17
    @11
    vw
    cU
    @15
    @6
    cU
    wcel
    #
    wa
    #
    @17
    @11
    @20
    @17
    wa
    #
    @7
    @10
    @20
    @7
    @16
    simprl
    @21
    @9
    @4
    cV
    @21
    @6
    @8
    wss
    #
    @16
    @9
    @4
    wss
    @21
    @0
    @19
    @22
    @0
    @1
    @13
    @5
    @19
    @17
    simp-5l
    @15
    @19
    @17
    simplr
    cU
    @6
    cX
    ustssco
    syl2anc
    @20
    @7
    @16
    simprr
    @22
    @16
    wa
    #
    @9
    @6
    @3
    ccom
    #
    @4
    @16
    @9
    @24
    wss
    @22
    @8
    @3
    @6
    coss2
    adantl
    @23
    @6
    @3
    wss
    @24
    @4
    wss
    @6
    @8
    @3
    sstr
    @6
    @3
    @3
    coss1
    syl
    sstrd
    syl2anc
    @14
    @5
    @19
    @17
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
