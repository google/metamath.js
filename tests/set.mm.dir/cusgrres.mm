include "ccusgr.mm"
include "wcel.mm"
include "wa.mm"
include "cusgr.mm"
include "ccplgr.mm"
include "cusgrusgr.mm"
include "usgrres1.mm"
include "sylan.mm"
include "cv.mm"
include "cuvtx.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "iscusgr.mm"
include "cupgr.mm"
include "usgrupgr.mm"
include "adantr.mm"
include "anim1i.mm"
include "wi.mm"
include "iscplgr.mm"
include "eldifi.mm"
include "ad2antll.mm"
include "eleq1.mm"
include "rspcv.mm"
include "syl.mm"
include "ex.mm"
include "com23.mm"
include "sylbid.mm"
include "imp.mm"
include "impl.mm"
include "uvtxupgrres.mm"
include "sylc.mm"
include "ralrimiva.mm"
include "sylanb.mm"
include "cvv.mm"
include "wb.mm"
include "cid.mm"
include "cres.mm"
include "cop.mm"
include "opex.mm"
include "eqeltri.mm"
include "cvtx.mm"
include "upgrres1lem2.mm"
include "eqcomi.mm"
include "mp1i.mm"
include "mpbird.mm"
include "sylanbrc.mm"

theorem cusgrres
  let cS: class S
  let ve: setvar e
  let cE: class E
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let vn: setvar n
  let vv: setvar v
  assume cusgrres.v: |- V = ( Vtx ` G )
  assume cusgrres.e: |- E = ( Edg ` G )
  assume cusgrres.f: |- F = { e e. E | N e/ e }
  assume cusgrres.s: |- S = <. ( V \ { N } ) , ( _I |` F ) >.

  disjoint E e
  disjoint G e
  disjoint N e
  disjoint V e
  disjoint G n
  disjoint G v
  disjoint e n
  disjoint e v
  disjoint n v
  disjoint N n
  disjoint N v
  disjoint S n
  disjoint S v
  disjoint V n
  disjoint V v
  assert |- ( ( G e. ComplUSGraph /\ N e. V ) -> S e. ComplUSGraph )

  proof
    cG
    ccusgr
    wcel
    #
    cN
    cV
    wcel
    #
    wa
    #
    cS
    cusgr
    wcel
    #
    cS
    ccplgr
    wcel
    #
    cS
    ccusgr
    wcel
    @0
    cG
    cusgr
    wcel
    #
    @1
    @3
    cG
    cusgrusgr
    cS
    ve
    cE
    cF
    cG
    cN
    cV
    cusgrres.v
    cusgrres.e
    cusgrres.f
    cusgrres.s
    usgrres1
    sylan
    @2
    @4
    vv
    cv
    #
    cS
    cuvtx
    cfv
    wcel
    #
    vv
    cV
    cN
    csn
    #
    cdif
    #
    wral
    #
    @0
    @5
    cG
    ccplgr
    wcel
    #
    wa
    #
    @1
    @10
    cG
    iscusgr
    @12
    @1
    wa
    #
    @7
    vv
    @9
    @13
    @6
    @9
    wcel
    #
    wa
    cG
    cupgr
    wcel
    #
    @1
    wa
    #
    @14
    wa
    @6
    cG
    cuvtx
    cfv
    #
    wcel
    #
    @7
    @13
    @16
    @14
    @12
    @15
    @1
    @5
    @15
    @11
    cG
    usgrupgr
    adantr
    anim1i
    anim1i
    @12
    @1
    @14
    @18
    @5
    @11
    @1
    @14
    wa
    #
    @18
    wi
    #
    @5
    @11
    vn
    cv
    #
    @17
    wcel
    #
    vn
    cV
    wral
    #
    @20
    vn
    cG
    cV
    cusgr
    cusgrres.v
    iscplgr
    @5
    @19
    @23
    @18
    @5
    @19
    @23
    @18
    wi
    #
    @5
    @19
    wa
    @6
    cV
    wcel
    #
    @24
    @14
    @25
    @5
    @1
    @6
    cV
    @8
    eldifi
    ad2antll
    @22
    @18
    vn
    @6
    cV
    @21
    @6
    @17
    eleq1
    rspcv
    syl
    ex
    com23
    sylbid
    imp
    impl
    cS
    ve
    cE
    cF
    cG
    @6
    cN
    cV
    cusgrres.v
    cusgrres.e
    cusgrres.f
    cusgrres.s
    uvtxupgrres
    sylc
    ralrimiva
    sylanb
    cS
    cvv
    wcel
    @4
    @10
    wb
    @2
    cS
    @9
    cid
    cF
    cres
    #
    cop
    cvv
    cusgrres.s
    @9
    @26
    opex
    eqeltri
    vv
    cS
    @9
    cvv
    cS
    cvtx
    cfv
    @9
    cS
    ve
    cE
    cF
    cG
    cN
    cV
    cusgrres.v
    cusgrres.e
    cusgrres.f
    cusgrres.s
    upgrres1lem2
    eqcomi
    iscplgr
    mp1i
    mpbird
    cS
    iscusgr
    sylanbrc
end
