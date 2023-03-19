include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cv.mm"
include "wn.mm"
include "wrex.mm"
include "co.mm"
include "wceq.mm"
include "lhpexnle.mm"
include "adantr.mm"
include "w3a.mm"
include "wne.mm"
include "cdlemf1.mm"
include "wi.mm"
include "simpr1r.mm"
include "simpr32.mm"
include "simpr33.mm"
include "simplrr.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wb.mm"
include "hllat.mm"
include "ad3antrrr.mm"
include "simplrl.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simplll.mm"
include "simpr1l.mm"
include "simpr2.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "lhpbase.mm"
include "ad3antlr.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "cal.mm"
include "hlatl.mm"
include "simpll.mm"
include "simpr31.mm"
include "lhpat.mm"
include "syl122anc.mm"
include "atcmp.mm"
include "mpbid.mm"
include "jca31.mm"
include "3exp2.mm"
include "3impia.mm"
include "reximdvai.mm"
include "mpd.mm"
include "3expia.mm"
include "expd.mm"

theorem cdlemf2
  let cA: class A
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vq: setvar q
  let vp: setvar p
  let cP: class P
  assume cdlemf1.l: |- .<_ = ( le ` K )
  assume cdlemf1.j: |- .\/ = ( join ` K )
  assume cdlemf1.a: |- A = ( Atoms ` K )
  assume cdlemf1.h: |- H = ( LHyp ` K )
  assume cdlemf2.m: |- ./\ = ( meet ` K )

  disjoint p q
  disjoint A p
  disjoint A q
  disjoint H p
  disjoint H q
  disjoint K p
  disjoint K q
  disjoint .<_ p
  disjoint .<_ q
  disjoint U p
  disjoint U q
  disjoint W p
  disjoint W q
  disjoint P q
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( U e. A /\ U .<_ W ) ) -> E. p e. A E. q e. A ( ( -. p .<_ W /\ -. q .<_ W ) /\ U = ( ( p .\/ q ) ./\ W ) ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cU
    cA
    wcel
    #
    cU
    cW
    c.le
    wbr
    #
    wa
    #
    wa
    #
    vp
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    vp
    cA
    wrex
    #
    @8
    vq
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    wa
    cU
    @7
    @10
    c.or
    co
    #
    cW
    c.an
    co
    #
    wceq
    #
    wa
    #
    vq
    cA
    wrex
    #
    vp
    cA
    wrex
    @2
    @9
    @5
    cA
    cH
    cK
    c.le
    cW
    vp
    cdlemf1.l
    cdlemf1.a
    cdlemf1.h
    lhpexnle
    adantr
    @6
    @8
    @16
    vp
    cA
    @6
    @7
    cA
    wcel
    #
    @8
    @16
    @2
    @5
    @17
    @8
    wa
    #
    @16
    @2
    @5
    @18
    w3a
    #
    @7
    @10
    wne
    #
    @11
    cU
    @12
    c.le
    wbr
    #
    w3a
    #
    vq
    cA
    wrex
    @16
    cA
    @7
    cU
    cH
    c.or
    cK
    c.le
    cW
    vq
    cdlemf1.l
    cdlemf1.j
    cdlemf1.a
    cdlemf1.h
    cdlemf1
    @19
    @22
    @15
    vq
    cA
    @2
    @5
    @18
    @10
    cA
    wcel
    #
    @22
    @15
    wi
    wi
    @6
    @18
    @23
    @22
    @15
    @6
    @18
    @23
    @22
    w3a
    #
    wa
    #
    @8
    @11
    @14
    @17
    @8
    @23
    @22
    @6
    simpr1r
    #
    @20
    @11
    @21
    @18
    @23
    @6
    simpr32
    @25
    cU
    @13
    c.le
    wbr
    #
    @14
    @25
    @21
    @4
    @27
    @20
    @11
    @21
    @18
    @23
    @6
    simpr33
    @2
    @3
    @4
    @24
    simplrr
    @25
    cK
    clat
    wcel
    #
    cU
    cK
    cbs
    cfv
    #
    wcel
    #
    @12
    @29
    wcel
    #
    cW
    @29
    wcel
    #
    @21
    @4
    wa
    @27
    wb
    @0
    @28
    @1
    @5
    @24
    cK
    hllat
    ad3antrrr
    @25
    @3
    @30
    @2
    @3
    @4
    @24
    simplrl
    #
    cA
    @29
    cU
    cK
    @29
    eqid
    #
    cdlemf1.a
    atbase
    syl
    @25
    @0
    @17
    @23
    @31
    @0
    @1
    @5
    @24
    simplll
    @17
    @8
    @23
    @22
    @6
    simpr1l
    #
    @6
    @18
    @23
    @22
    simpr2
    #
    cA
    @29
    c.or
    cK
    @7
    @10
    @34
    cdlemf1.j
    cdlemf1.a
    hlatjcl
    syl3anc
    @1
    @32
    @0
    @5
    @24
    @29
    cH
    cK
    cW
    @34
    cdlemf1.h
    lhpbase
    ad3antlr
    @29
    cK
    c.le
    c.an
    cU
    @12
    cW
    @34
    cdlemf1.l
    cdlemf2.m
    latlem12
    syl13anc
    mpbi2and
    @25
    cK
    cal
    wcel
    #
    @3
    @13
    cA
    wcel
    #
    @27
    @14
    wb
    @0
    @37
    @1
    @5
    @24
    cK
    hlatl
    ad3antrrr
    @33
    @25
    @2
    @17
    @8
    @23
    @20
    @38
    @2
    @5
    @24
    simpll
    @35
    @26
    @36
    @20
    @11
    @21
    @18
    @23
    @6
    simpr31
    cA
    @7
    @10
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemf1.l
    cdlemf1.j
    cdlemf2.m
    cdlemf1.a
    cdlemf1.h
    lhpat
    syl122anc
    cA
    cU
    @13
    cK
    c.le
    cdlemf1.l
    cdlemf1.a
    atcmp
    syl3anc
    mpbid
    jca31
    3exp2
    3impia
    reximdvai
    mpd
    3expia
    expd
    reximdvai
    mpd
end
