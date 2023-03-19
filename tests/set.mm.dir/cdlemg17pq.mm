include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "simp11.mm"
include "simp13.mm"
include "simp12.mm"
include "3jca.mm"
include "simp21.mm"
include "simp22.mm"
include "simp23.mm"
include "necomd.mm"
include "simp31.mm"
include "ltrnatneq.mm"
include "syl131anc.mm"
include "simp32.mm"
include "simp11l.mm"
include "simp12l.mm"
include "simp13l.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "breqtrd.mm"
include "simp33.mm"
include "eqcom.mm"
include "anbi2i.mm"
include "rexbii.mm"
include "sylnib.mm"

theorem cdlemg17pq
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vr: setvar r
  let cS: class S
  assume cdlemg12.l: |- .<_ = ( le ` K )
  assume cdlemg12.j: |- .\/ = ( join ` K )
  assume cdlemg12.m: |- ./\ = ( meet ` K )
  assume cdlemg12.a: |- A = ( Atoms ` K )
  assume cdlemg12.h: |- H = ( LHyp ` K )
  assume cdlemg12.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg12b.r: |- R = ( ( trL ` K ) ` W )

  disjoint A r
  disjoint G r
  disjoint .\/ r
  disjoint .<_ r
  disjoint P r
  disjoint Q r
  disjoint W r
  disjoint F r
  disjoint S r
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T /\ P =/= Q ) /\ ( ( G ` P ) =/= P /\ ( R ` G ) .<_ ( P .\/ Q ) /\ -. E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( P e. A /\ -. P .<_ W ) ) /\ ( F e. T /\ G e. T /\ Q =/= P ) /\ ( ( G ` Q ) =/= Q /\ ( R ` G ) .<_ ( Q .\/ P ) /\ -. E. r e. A ( -. r .<_ W /\ ( Q .\/ r ) = ( P .\/ r ) ) ) ) )

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
    cF
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    cP
    cQ
    wne
    #
    w3a
    #
    cP
    cG
    cfv
    cP
    wne
    #
    cG
    cR
    cfv
    #
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    vr
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    cP
    @18
    c.or
    co
    #
    cQ
    @18
    c.or
    co
    #
    wceq
    #
    wa
    #
    vr
    cA
    wrex
    #
    wn
    #
    w3a
    #
    w3a
    #
    @2
    @8
    @5
    w3a
    @10
    @11
    cQ
    cP
    wne
    #
    w3a
    cQ
    cG
    cfv
    cQ
    wne
    #
    @15
    cQ
    cP
    c.or
    co
    #
    c.le
    wbr
    #
    @19
    @21
    @20
    wceq
    #
    wa
    #
    vr
    cA
    wrex
    #
    wn
    #
    w3a
    @27
    @2
    @8
    @5
    @2
    @5
    @8
    @13
    @26
    simp11
    #
    @2
    @5
    @8
    @13
    @26
    simp13
    #
    @2
    @5
    @8
    @13
    @26
    simp12
    #
    3jca
    @27
    @10
    @11
    @28
    @9
    @10
    @11
    @12
    @26
    simp21
    @9
    @10
    @11
    @12
    @26
    simp22
    #
    @27
    cP
    cQ
    @9
    @10
    @11
    @12
    @26
    simp23
    necomd
    3jca
    @27
    @29
    @31
    @35
    @27
    @2
    @11
    @5
    @8
    @14
    @29
    @36
    @39
    @38
    @37
    @9
    @13
    @14
    @17
    @25
    simp31
    cA
    cP
    cQ
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemg12.l
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    ltrnatneq
    syl131anc
    @27
    @15
    @16
    @30
    c.le
    @9
    @13
    @14
    @17
    @25
    simp32
    @27
    @0
    @3
    @6
    @16
    @30
    wceq
    @0
    @1
    @5
    @8
    @13
    @26
    simp11l
    @3
    @4
    @2
    @8
    @13
    @26
    simp12l
    @6
    @7
    @2
    @5
    @13
    @26
    simp13l
    cA
    c.or
    cK
    cP
    cQ
    cdlemg12.j
    cdlemg12.a
    hlatjcom
    syl3anc
    breqtrd
    @27
    @24
    @34
    @9
    @13
    @14
    @17
    @25
    simp33
    @23
    @33
    vr
    cA
    @22
    @32
    @19
    @20
    @21
    eqcom
    anbi2i
    rexbii
    sylnib
    3jca
    3jca
end
