include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "cp0.mm"
include "wceq.mm"
include "wo.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp22.mm"
include "simp23l.mm"
include "simp31.mm"
include "cdlemg31b0a.mm"
include "syl132anc.mm"
include "simp23r.mm"
include "adantr.mm"
include "wb.mm"
include "cal.mm"
include "simp11l.mm"
include "hlatl.mm"
include "syl.mm"
include "simpl21.mm"
include "simpr.mm"
include "atcmp.mm"
include "syl3anc.mm"
include "necon3bbid.mm"
include "eqid.mm"
include "atnle0.mm"
include "syl2anc.mm"
include "breq2d.mm"
include "mtbird.mm"
include "2thd.mm"
include "jaodan.mm"
include "mpbird.mm"
include "mpdan.mm"
include "simp32.mm"
include "clat.mm"
include "cbs.mm"
include "hllat.mm"
include "simp21.mm"
include "atbase.mm"
include "simp12l.mm"
include "simp22l.mm"
include "hlatjcl.mm"
include "simp13l.mm"
include "simp33.mm"
include "trlat.mm"
include "syl112anc.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "breq2i.mm"
include "syl6bbr.mm"
include "biimpd.mm"
include "mpand.mm"
include "mtod.mm"
include "wi.mm"
include "trlle.mm"
include "simp13r.mm"
include "nbrne2.mm"
include "hlatexch1.mm"
include "syl131anc.mm"

theorem cdlemg27b
  let vz: setvar z
  let vv: setvar v
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let vr: setvar r
  let cG: class G
  let cS: class S
  assume cdlemg12.l: |- .<_ = ( le ` K )
  assume cdlemg12.j: |- .\/ = ( join ` K )
  assume cdlemg12.m: |- ./\ = ( meet ` K )
  assume cdlemg12.a: |- A = ( Atoms ` K )
  assume cdlemg12.h: |- H = ( LHyp ` K )
  assume cdlemg12.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg12b.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemg31.n: |- N = ( ( P .\/ v ) ./\ ( Q .\/ ( R ` F ) ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( z e. A /\ ( v e. A /\ v .<_ W ) /\ ( F e. T /\ z =/= N ) ) /\ ( v =/= ( R ` F ) /\ z .<_ ( P .\/ v ) /\ ( F ` P ) =/= P ) ) -> -. ( R ` F ) .<_ ( Q .\/ z ) )

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
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cQ
    cA
    wcel
    #
    cQ
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    vz
    cv
    #
    cA
    wcel
    #
    vv
    cv
    #
    cA
    wcel
    #
    @12
    cW
    c.le
    wbr
    #
    wa
    #
    cF
    cT
    wcel
    #
    @10
    cN
    wne
    #
    wa
    #
    w3a
    #
    @12
    cF
    cR
    cfv
    #
    wne
    #
    @10
    cP
    @12
    c.or
    co
    #
    c.le
    wbr
    #
    cP
    cF
    cfv
    cP
    wne
    #
    w3a
    #
    w3a
    #
    @20
    cQ
    @10
    c.or
    co
    c.le
    wbr
    #
    @10
    cQ
    @20
    c.or
    co
    #
    c.le
    wbr
    #
    @26
    @29
    @10
    cN
    c.le
    wbr
    #
    @26
    cN
    cA
    wcel
    #
    cN
    cK
    cp0
    cfv
    #
    wceq
    #
    wo
    #
    @30
    wn
    #
    @26
    @2
    @5
    @8
    @15
    @16
    @21
    @34
    @2
    @5
    @8
    @19
    @25
    simp11
    #
    @2
    @5
    @8
    @19
    @25
    simp12
    #
    @2
    @5
    @8
    @19
    @25
    simp13
    @9
    @11
    @15
    @18
    @25
    simp22
    @16
    @17
    @11
    @15
    @9
    @25
    simp23l
    #
    @9
    @19
    @21
    @23
    @24
    simp31
    vv
    cA
    cP
    cQ
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg31.n
    cdlemg31b0a
    syl132anc
    @26
    @34
    wa
    @35
    @17
    @26
    @17
    @34
    @16
    @17
    @11
    @15
    @9
    @25
    simp23r
    #
    adantr
    @26
    @31
    @35
    @17
    wb
    @33
    @26
    @31
    wa
    #
    @30
    @10
    cN
    @40
    cK
    cal
    wcel
    #
    @11
    @31
    @30
    @10
    cN
    wceq
    wb
    @40
    @0
    @41
    @26
    @0
    @31
    @0
    @1
    @5
    @8
    @19
    @25
    simp11l
    #
    adantr
    cK
    hlatl
    #
    syl
    @11
    @15
    @18
    @9
    @25
    @31
    simpl21
    @26
    @31
    simpr
    cA
    @10
    cN
    cK
    c.le
    cdlemg12.l
    cdlemg12.a
    atcmp
    syl3anc
    necon3bbid
    @26
    @33
    wa
    #
    @35
    @17
    @44
    @30
    @10
    @32
    c.le
    wbr
    #
    @44
    @41
    @11
    @45
    wn
    @44
    @0
    @41
    @26
    @0
    @33
    @42
    adantr
    @43
    syl
    @11
    @15
    @18
    @9
    @25
    @33
    simpl21
    cA
    @10
    cK
    c.le
    @32
    cdlemg12.l
    @32
    eqid
    cdlemg12.a
    atnle0
    syl2anc
    @44
    cN
    @32
    @10
    c.le
    @26
    @33
    simpr
    breq2d
    mtbird
    @26
    @17
    @33
    @39
    adantr
    2thd
    jaodan
    mpbird
    mpdan
    @26
    @23
    @29
    @30
    @9
    @19
    @21
    @23
    @24
    simp32
    @26
    @23
    @29
    wa
    #
    @30
    @26
    @46
    @10
    @22
    @28
    c.an
    co
    #
    c.le
    wbr
    #
    @30
    @26
    cK
    clat
    wcel
    #
    @10
    cK
    cbs
    cfv
    #
    wcel
    #
    @22
    @50
    wcel
    #
    @28
    @50
    wcel
    #
    @46
    @48
    wb
    @26
    @0
    @49
    @42
    cK
    hllat
    syl
    @26
    @11
    @51
    @9
    @11
    @15
    @18
    @25
    simp21
    #
    cA
    @50
    @10
    cK
    @50
    eqid
    #
    cdlemg12.a
    atbase
    syl
    @26
    @0
    @3
    @13
    @52
    @42
    @3
    @4
    @2
    @8
    @19
    @25
    simp12l
    @13
    @14
    @11
    @18
    @9
    @25
    simp22l
    cA
    @50
    c.or
    cK
    cP
    @12
    @55
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    @26
    @0
    @6
    @20
    cA
    wcel
    #
    @53
    @42
    @6
    @7
    @2
    @5
    @19
    @25
    simp13l
    #
    @26
    @2
    @5
    @16
    @24
    @56
    @36
    @37
    @38
    @9
    @19
    @21
    @23
    @24
    simp33
    cA
    cP
    cR
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg12.l
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    trlat
    syl112anc
    #
    cA
    @50
    c.or
    cK
    cQ
    @20
    @55
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    @50
    cK
    c.le
    c.an
    @10
    @22
    @28
    @55
    cdlemg12.l
    cdlemg12.m
    latlem12
    syl13anc
    cN
    @47
    @10
    c.le
    cdlemg31.n
    breq2i
    syl6bbr
    biimpd
    mpand
    mtod
    @26
    @0
    @56
    @11
    @6
    @20
    cQ
    wne
    #
    @27
    @29
    wi
    @42
    @58
    @54
    @57
    @26
    @20
    cW
    c.le
    wbr
    #
    @7
    @59
    @26
    @2
    @16
    @60
    @36
    @38
    cR
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg12.l
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    trlle
    syl2anc
    @6
    @7
    @2
    @5
    @19
    @25
    simp13r
    @20
    cQ
    cW
    c.le
    nbrne2
    syl2anc
    cA
    @20
    @10
    cQ
    c.or
    cK
    c.le
    cdlemg12.l
    cdlemg12.j
    cdlemg12.a
    hlatexch1
    syl131anc
    mtod
end
