include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "co.mm"
include "cp0.mm"
include "wceq.mm"
include "wo.mm"
include "simp11.mm"
include "simp2ll.mm"
include "simp31l.mm"
include "simp2rl.mm"
include "simp12.mm"
include "jca.mm"
include "simp2l.mm"
include "simp13.mm"
include "simp33.mm"
include "trlat.mm"
include "syl112anc.mm"
include "simp2r.mm"
include "trlle.mm"
include "syl2anc.mm"
include "simp31.mm"
include "simp32.mm"
include "necomd.mm"
include "lhp2atne.mm"
include "syl321anc.mm"
include "eqid.mm"
include "2atmat0.mm"
include "syl33anc.mm"
include "eleq1i.mm"
include "eqeq1i.mm"
include "orbi12i.mm"
include "sylibr.mm"

theorem cdlemg31b0N
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


  assert |- ( ( ( K e. HL /\ W e. H /\ F e. T ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( v e. A /\ v .<_ W ) /\ v =/= ( R ` F ) /\ ( F ` P ) =/= P ) ) -> ( N e. A \/ N = ( 0. ` K ) ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    cF
    cT
    wcel
    #
    w3a
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
    wa
    #
    vv
    cv
    #
    cA
    wcel
    #
    @11
    cW
    c.le
    wbr
    #
    wa
    #
    @11
    cF
    cR
    cfv
    #
    wne
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
    cP
    @11
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
    @22
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
    @24
    wceq
    #
    wo
    @19
    @0
    @4
    @12
    @7
    @15
    cA
    wcel
    #
    @20
    @21
    wne
    @26
    @0
    @1
    @2
    @10
    @18
    simp11
    #
    @4
    @5
    @9
    @3
    @18
    simp2ll
    #
    @12
    @13
    @16
    @17
    @3
    @10
    simp31l
    @7
    @8
    @6
    @3
    @18
    simp2rl
    @19
    @0
    @1
    wa
    #
    @6
    @2
    @17
    @29
    @19
    @0
    @1
    @30
    @0
    @1
    @2
    @10
    @18
    simp12
    jca
    #
    @3
    @6
    @9
    @18
    simp2l
    @0
    @1
    @2
    @10
    @18
    simp13
    #
    @3
    @10
    @14
    @16
    @17
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
    @19
    @21
    @20
    @19
    @32
    @9
    @4
    @29
    @15
    cW
    c.le
    wbr
    #
    wa
    @14
    @15
    @11
    wne
    @21
    @20
    wne
    @33
    @3
    @6
    @9
    @18
    simp2r
    @31
    @19
    @29
    @36
    @35
    @19
    @32
    @2
    @36
    @33
    @34
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
    @3
    @10
    @14
    @16
    @17
    simp31
    @19
    @11
    @15
    @3
    @10
    @14
    @16
    @17
    simp32
    necomd
    cA
    cQ
    cP
    @15
    cH
    c.or
    cK
    c.le
    @11
    cW
    cdlemg12.l
    cdlemg12.j
    cdlemg12.a
    cdlemg12.h
    lhp2atne
    syl321anc
    necomd
    cA
    cP
    @11
    cQ
    @15
    c.or
    cK
    c.an
    @24
    cdlemg12.j
    cdlemg12.m
    @24
    eqid
    cdlemg12.a
    2atmat0
    syl33anc
    @27
    @23
    @28
    @25
    cN
    @22
    cA
    cdlemg31.n
    eleq1i
    cN
    @22
    @24
    cdlemg31.n
    eqeq1i
    orbi12i
    sylibr
end
