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
include "simp1.mm"
include "simp21r.mm"
include "simp21l.mm"
include "jca.mm"
include "simp22.mm"
include "simp23.mm"
include "simp31.mm"
include "simp33.mm"
include "cdlemg17j.mm"
include "syl133anc.mm"
include "simp11.mm"
include "simp13.mm"
include "simp12.mm"
include "necomd.mm"
include "ltrnatneq.mm"
include "syl131anc.mm"
include "simp11l.mm"
include "simp12l.mm"
include "simp13l.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "breqtrd.mm"
include "eqcom.mm"
include "anbi2i.mm"
include "rexbii.mm"
include "sylnib.mm"
include "syl333anc.mm"
include "oveq12d.mm"
include "simp32.mm"
include "eqnetrrd.mm"
include "cdlemg19.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"

theorem cdlemg21
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( F e. T /\ G e. T ) /\ P =/= Q /\ ( F ` P ) =/= P ) /\ ( ( R ` F ) .<_ ( P .\/ Q ) /\ ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) =/= ( P .\/ Q ) /\ -. E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ W ) = ( ( Q .\/ ( F ` ( G ` Q ) ) ) ./\ W ) )

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
    wa
    #
    cP
    cQ
    wne
    #
    cP
    cF
    cfv
    #
    cP
    wne
    #
    w3a
    #
    cF
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
    cP
    cG
    cfv
    cF
    cfv
    #
    cQ
    cG
    cfv
    cF
    cfv
    #
    c.or
    co
    #
    @18
    wne
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
    @24
    c.or
    co
    #
    cQ
    @24
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
    cP
    @14
    cG
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    #
    cQ
    cQ
    cF
    cfv
    #
    cG
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    #
    cP
    @20
    c.or
    co
    #
    cW
    c.an
    co
    cQ
    @21
    c.or
    co
    #
    cW
    c.an
    co
    @33
    @9
    @11
    @10
    wa
    @13
    @15
    @19
    @34
    @38
    c.or
    co
    #
    @18
    wne
    @31
    @36
    @40
    wceq
    @9
    @16
    @32
    simp1
    #
    @33
    @11
    @10
    @10
    @11
    @13
    @15
    @9
    @32
    simp21r
    #
    @10
    @11
    @13
    @15
    @9
    @32
    simp21l
    #
    jca
    @9
    @12
    @13
    @15
    @32
    simp22
    #
    @9
    @12
    @13
    @15
    @32
    simp23
    #
    @9
    @16
    @19
    @23
    @31
    simp31
    #
    @33
    @22
    @43
    @18
    @33
    @20
    @34
    @21
    @38
    c.or
    @33
    @9
    @11
    @10
    @13
    @15
    @19
    @31
    @20
    @34
    wceq
    @44
    @45
    @46
    @47
    @48
    @49
    @9
    @16
    @19
    @23
    @31
    simp33
    #
    cA
    cP
    cQ
    cR
    cT
    cG
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    vr
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg17j
    syl133anc
    #
    @33
    @2
    @8
    @5
    @11
    @10
    cQ
    cP
    wne
    @37
    cQ
    wne
    #
    @17
    cQ
    cP
    c.or
    co
    #
    c.le
    wbr
    @25
    @27
    @26
    wceq
    #
    wa
    #
    vr
    cA
    wrex
    #
    wn
    @21
    @38
    wceq
    @2
    @5
    @8
    @16
    @32
    simp11
    #
    @2
    @5
    @8
    @16
    @32
    simp13
    #
    @2
    @5
    @8
    @16
    @32
    simp12
    #
    @45
    @46
    @33
    cP
    cQ
    @47
    necomd
    @33
    @2
    @10
    @5
    @8
    @15
    @52
    @57
    @46
    @59
    @58
    @48
    cA
    cP
    cQ
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
    ltrnatneq
    syl131anc
    @33
    @17
    @18
    @53
    c.le
    @49
    @33
    @0
    @3
    @6
    @18
    @53
    wceq
    @0
    @1
    @5
    @8
    @16
    @32
    simp11l
    @3
    @4
    @2
    @8
    @16
    @32
    simp12l
    @6
    @7
    @2
    @5
    @16
    @32
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
    @33
    @30
    @56
    @50
    @29
    @55
    vr
    cA
    @28
    @54
    @25
    @26
    @27
    eqcom
    anbi2i
    rexbii
    sylnib
    cA
    cQ
    cP
    cR
    cT
    cG
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    vr
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg17j
    syl333anc
    #
    oveq12d
    @9
    @16
    @19
    @23
    @31
    simp32
    eqnetrrd
    @50
    cA
    cP
    cQ
    cR
    cT
    cG
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    vr
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg19
    syl133anc
    @33
    @41
    @35
    cW
    c.an
    @33
    @20
    @34
    cP
    c.or
    @51
    oveq2d
    oveq1d
    @33
    @42
    @39
    cW
    c.an
    @33
    @21
    @38
    cQ
    c.or
    @60
    oveq2d
    oveq1d
    3eqtr4d
end
