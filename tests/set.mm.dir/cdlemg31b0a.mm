include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "w3a.mm"
include "cfv.mm"
include "wne.mm"
include "co.mm"
include "cp0.mm"
include "wceq.mm"
include "wo.mm"
include "simp1l.mm"
include "simp21l.mm"
include "simp23l.mm"
include "simp22l.mm"
include "simp1.mm"
include "simp3l.mm"
include "eqid.mm"
include "trlator0.mm"
include "syl2anc.mm"
include "simp22.mm"
include "trlle.mm"
include "jca.mm"
include "simp23.mm"
include "simp3r.mm"
include "necomd.mm"
include "lhp2at0ne.mm"
include "syl321anc.mm"
include "2at0mat0.mm"
include "syl33anc.mm"
include "eleq1i.mm"
include "eqeq1i.mm"
include "orbi12i.mm"
include "sylibr.mm"

theorem cdlemg31b0a
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( v e. A /\ v .<_ W ) ) /\ ( F e. T /\ v =/= ( R ` F ) ) ) -> ( N e. A \/ N = ( 0. ` K ) ) )

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
    vv
    cv
    #
    cA
    wcel
    #
    @9
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
    @9
    cF
    cR
    cfv
    #
    wne
    #
    wa
    #
    w3a
    #
    cP
    @9
    c.or
    co
    #
    cQ
    @15
    c.or
    co
    #
    c.an
    co
    #
    cA
    wcel
    #
    @21
    cK
    cp0
    cfv
    #
    wceq
    #
    wo
    #
    cN
    cA
    wcel
    #
    cN
    @23
    wceq
    #
    wo
    @18
    @0
    @3
    @10
    @6
    @15
    cA
    wcel
    @15
    @23
    wceq
    wo
    #
    @19
    @20
    wne
    @25
    @0
    @1
    @13
    @17
    simp1l
    @3
    @4
    @8
    @12
    @2
    @17
    simp21l
    #
    @10
    @11
    @5
    @8
    @2
    @17
    simp23l
    @6
    @7
    @5
    @12
    @2
    @17
    simp22l
    @18
    @2
    @14
    @28
    @2
    @13
    @17
    simp1
    #
    @2
    @13
    @14
    @16
    simp3l
    #
    cA
    cR
    cT
    cF
    cH
    cK
    cW
    @23
    @23
    eqid
    #
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    trlator0
    syl2anc
    #
    @18
    @20
    @19
    @18
    @2
    @8
    @3
    @28
    @15
    cW
    c.le
    wbr
    #
    wa
    @12
    @15
    @9
    wne
    @20
    @19
    wne
    @30
    @2
    @5
    @8
    @12
    @17
    simp22
    @29
    @18
    @28
    @34
    @33
    @18
    @2
    @14
    @34
    @30
    @31
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
    jca
    @2
    @5
    @8
    @12
    @17
    simp23
    @18
    @9
    @15
    @2
    @13
    @14
    @16
    simp3r
    necomd
    cA
    cQ
    cP
    @15
    cH
    c.or
    cK
    c.le
    @9
    cW
    @23
    cdlemg12.l
    cdlemg12.j
    @32
    cdlemg12.a
    cdlemg12.h
    lhp2at0ne
    syl321anc
    necomd
    cA
    cP
    @9
    cQ
    @15
    c.or
    cK
    c.an
    @23
    cdlemg12.j
    cdlemg12.m
    @32
    cdlemg12.a
    2at0mat0
    syl33anc
    @26
    @22
    @27
    @24
    cN
    @21
    cA
    cdlemg31.n
    eleq1i
    cN
    @21
    @23
    cdlemg31.n
    eqeq1i
    orbi12i
    sylibr
end
