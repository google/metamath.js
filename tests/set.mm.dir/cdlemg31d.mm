include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "w3a.mm"
include "cfv.mm"
include "wne.mm"
include "wceq.mm"
include "simp22r.mm"
include "adantr.mm"
include "co.mm"
include "simpl1.mm"
include "simp21l.mm"
include "simp22l.mm"
include "simp23l.mm"
include "simpl31.mm"
include "cdlemg31b.mm"
include "syl122anc.mm"
include "cp0.mm"
include "simpl21.mm"
include "simpr.mm"
include "eqid.mm"
include "trl0.mm"
include "syl112anc.mm"
include "oveq2d.mm"
include "col.mm"
include "cbs.mm"
include "simp1l.mm"
include "hlol.mm"
include "syl.mm"
include "atbase.mm"
include "olj01.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "cal.mm"
include "wb.mm"
include "hlatl.mm"
include "simpl33.mm"
include "atcmp.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "breq1d.mm"
include "mtbird.mm"
include "simpl22.mm"
include "simpl23.mm"
include "simpl32.mm"
include "cdlemg31c.mm"
include "syl323anc.mm"
include "pm2.61dane.mm"

theorem cdlemg31d
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( v e. A /\ v .<_ W ) ) /\ ( F e. T /\ v =/= ( R ` F ) /\ N e. A ) ) -> -. N .<_ W )

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
    #
    wn
    #
    wa
    #
    vv
    cv
    #
    cA
    wcel
    #
    @10
    cW
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    cF
    cT
    wcel
    #
    @10
    cF
    cR
    cfv
    #
    wne
    #
    cN
    cA
    wcel
    #
    w3a
    #
    w3a
    #
    cN
    cW
    c.le
    wbr
    #
    wn
    #
    cP
    cF
    cfv
    #
    cP
    @20
    @23
    cP
    wceq
    #
    wa
    #
    @21
    @7
    @20
    @8
    @24
    @6
    @8
    @5
    @13
    @2
    @19
    simp22r
    adantr
    @25
    cN
    cQ
    cW
    c.le
    @25
    cN
    cQ
    c.le
    wbr
    #
    cN
    cQ
    wceq
    #
    @25
    cN
    cQ
    @16
    c.or
    co
    #
    cQ
    c.le
    @25
    @2
    @3
    @6
    @11
    @15
    cN
    @28
    c.le
    wbr
    @2
    @14
    @19
    @24
    simpl1
    #
    @20
    @3
    @24
    @3
    @4
    @9
    @13
    @2
    @19
    simp21l
    adantr
    @20
    @6
    @24
    @6
    @8
    @5
    @13
    @2
    @19
    simp22l
    adantr
    #
    @20
    @11
    @24
    @11
    @12
    @5
    @9
    @2
    @19
    simp23l
    adantr
    @15
    @17
    @18
    @2
    @14
    @24
    simpl31
    #
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
    cdlemg31b
    syl122anc
    @25
    @28
    cQ
    cK
    cp0
    cfv
    #
    c.or
    co
    #
    cQ
    @25
    @16
    @32
    cQ
    c.or
    @25
    @2
    @5
    @15
    @24
    @16
    @32
    wceq
    @29
    @5
    @9
    @13
    @2
    @19
    @24
    simpl21
    @31
    @20
    @24
    simpr
    cA
    cP
    cR
    cT
    cF
    cH
    cK
    c.le
    cW
    @32
    cdlemg12.l
    @32
    eqid
    #
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    trl0
    syl112anc
    oveq2d
    @25
    cK
    col
    wcel
    #
    cQ
    cK
    cbs
    cfv
    #
    wcel
    #
    @33
    cQ
    wceq
    @20
    @35
    @24
    @20
    @0
    @35
    @0
    @1
    @14
    @19
    simp1l
    #
    cK
    hlol
    syl
    adantr
    @25
    @6
    @37
    @30
    cA
    @36
    cQ
    cK
    @36
    eqid
    #
    cdlemg12.a
    atbase
    syl
    @36
    c.or
    cK
    cQ
    @32
    @39
    cdlemg12.j
    @34
    olj01
    syl2anc
    eqtrd
    breqtrd
    @25
    cK
    cal
    wcel
    #
    @18
    @6
    @26
    @27
    wb
    @20
    @40
    @24
    @20
    @0
    @40
    @38
    cK
    hlatl
    syl
    adantr
    @15
    @17
    @18
    @2
    @14
    @24
    simpl33
    @30
    cA
    cN
    cQ
    cK
    c.le
    cdlemg12.l
    cdlemg12.a
    atcmp
    syl3anc
    mpbid
    breq1d
    mtbird
    @20
    @23
    cP
    wne
    #
    wa
    @2
    @5
    @9
    @13
    @15
    @17
    @41
    @18
    @22
    @2
    @14
    @19
    @41
    simpl1
    @5
    @9
    @13
    @2
    @19
    @41
    simpl21
    @5
    @9
    @13
    @2
    @19
    @41
    simpl22
    @5
    @9
    @13
    @2
    @19
    @41
    simpl23
    @15
    @17
    @18
    @2
    @14
    @41
    simpl31
    @15
    @17
    @18
    @2
    @14
    @41
    simpl32
    @20
    @41
    simpr
    @15
    @17
    @18
    @2
    @14
    @41
    simpl33
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
    cdlemg31c
    syl323anc
    pm2.61dane
end
