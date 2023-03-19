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
include "ccnv.mm"
include "wo.mm"
include "simp11l.mm"
include "simp23r.mm"
include "cbs.mm"
include "wb.mm"
include "simp11.mm"
include "simp22l.mm"
include "simp21l.mm"
include "ltrncnvat.mm"
include "syl3anc.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simp12l.mm"
include "simp13l.mm"
include "hlatjcl.mm"
include "ltrnle.mm"
include "syl112anc.mm"
include "wf1o.mm"
include "ltrn1o.mm"
include "syl2anc.mm"
include "f1ocnvfv2.mm"
include "ltrnj.mm"
include "breq12d.mm"
include "bitr2d.mm"
include "mpbid.mm"
include "simp33.mm"
include "simp23l.mm"
include "simp21.mm"
include "ltrncnvel.mm"
include "cdleme0nex.mm"
include "syl331anc.mm"
include "eqcom.mm"
include "f1ocnvfvb.mm"
include "syl5rbbr.mm"
include "orbi12d.mm"

theorem cdlemg17h
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( F e. T /\ G e. T ) /\ ( P =/= Q /\ S .<_ ( ( F ` P ) .\/ ( F ` Q ) ) ) ) /\ ( ( G ` P ) =/= P /\ ( R ` G ) .<_ ( P .\/ Q ) /\ -. E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> ( S = ( F ` P ) \/ S = ( F ` Q ) ) )

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
    cS
    cA
    wcel
    #
    cS
    cW
    c.le
    wbr
    wn
    #
    wa
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
    cS
    cP
    cF
    cfv
    #
    cQ
    cF
    cfv
    #
    c.or
    co
    #
    c.le
    wbr
    #
    wa
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
    cP
    @26
    c.or
    co
    cQ
    @26
    c.or
    co
    wceq
    wa
    vr
    cA
    wrex
    wn
    #
    w3a
    #
    w3a
    #
    cS
    cF
    ccnv
    cfv
    #
    cP
    wceq
    #
    @30
    cQ
    wceq
    #
    wo
    #
    cS
    @17
    wceq
    #
    cS
    @18
    wceq
    #
    wo
    @29
    @0
    @30
    @24
    c.le
    wbr
    #
    @27
    @3
    @6
    @16
    @30
    cA
    wcel
    #
    @30
    cW
    c.le
    wbr
    wn
    wa
    #
    @33
    @0
    @1
    @5
    @8
    @22
    @28
    simp11l
    #
    @29
    @20
    @36
    @16
    @20
    @12
    @15
    @9
    @28
    simp23r
    @29
    @36
    @30
    cF
    cfv
    #
    @24
    cF
    cfv
    #
    c.le
    wbr
    #
    @20
    @29
    @2
    @13
    @30
    cK
    cbs
    cfv
    #
    wcel
    #
    @24
    @43
    wcel
    #
    @36
    @42
    wb
    @2
    @5
    @8
    @22
    @28
    simp11
    #
    @13
    @14
    @12
    @21
    @9
    @28
    simp22l
    #
    @29
    @37
    @44
    @29
    @2
    @13
    @10
    @37
    @46
    @47
    @10
    @11
    @15
    @21
    @9
    @28
    simp21l
    #
    cA
    cS
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
    ltrncnvat
    syl3anc
    cA
    @43
    @30
    cK
    @43
    eqid
    #
    cdlemg12.a
    atbase
    syl
    @29
    @0
    @3
    @6
    @45
    @39
    @3
    @4
    @2
    @8
    @22
    @28
    simp12l
    #
    @6
    @7
    @2
    @5
    @22
    @28
    simp13l
    #
    cA
    @43
    c.or
    cK
    cP
    cQ
    @49
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    @43
    cT
    cF
    cH
    cK
    c.le
    chlt
    cW
    @30
    @24
    @49
    cdlemg12.l
    cdlemg12.h
    cdlemg12.t
    ltrnle
    syl112anc
    @29
    @40
    cS
    @41
    @19
    c.le
    @29
    @43
    @43
    cF
    wf1o
    #
    cS
    @43
    wcel
    #
    @40
    cS
    wceq
    @29
    @2
    @13
    @52
    @46
    @47
    @43
    cT
    cF
    cH
    cK
    chlt
    cW
    @49
    cdlemg12.h
    cdlemg12.t
    ltrn1o
    syl2anc
    #
    @29
    @10
    @53
    @48
    cA
    @43
    cS
    cK
    @49
    cdlemg12.a
    atbase
    syl
    #
    @43
    @43
    cS
    cF
    f1ocnvfv2
    syl2anc
    @29
    @2
    @13
    cP
    @43
    wcel
    #
    cQ
    @43
    wcel
    #
    @41
    @19
    wceq
    @46
    @47
    @29
    @3
    @56
    @50
    cA
    @43
    cP
    cK
    @49
    cdlemg12.a
    atbase
    syl
    #
    @29
    @6
    @57
    @51
    cA
    @43
    cQ
    cK
    @49
    cdlemg12.a
    atbase
    syl
    #
    @43
    cT
    cF
    cH
    c.or
    cK
    cW
    cP
    cQ
    @49
    cdlemg12.j
    cdlemg12.h
    cdlemg12.t
    ltrnj
    syl112anc
    breq12d
    bitr2d
    mpbid
    @9
    @22
    @23
    @25
    @27
    simp33
    @50
    @51
    @16
    @20
    @12
    @15
    @9
    @28
    simp23l
    @29
    @2
    @13
    @12
    @38
    @46
    @47
    @9
    @12
    @15
    @21
    @28
    simp21
    cA
    cS
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
    ltrncnvel
    syl3anc
    cA
    cP
    cQ
    @30
    c.or
    cK
    c.le
    cW
    vr
    cdlemg12.l
    cdlemg12.j
    cdlemg12.a
    cdleme0nex
    syl331anc
    @29
    @31
    @34
    @32
    @35
    @34
    @17
    cS
    wceq
    #
    @29
    @31
    @17
    cS
    eqcom
    @29
    @52
    @56
    @53
    @60
    @31
    wb
    @54
    @58
    @55
    @43
    @43
    cP
    cS
    cF
    f1ocnvfvb
    syl3anc
    syl5rbbr
    @35
    @18
    cS
    wceq
    #
    @29
    @32
    @18
    cS
    eqcom
    @29
    @52
    @57
    @53
    @61
    @32
    wb
    @54
    @59
    @55
    @43
    @43
    cQ
    cS
    cF
    f1ocnvfvb
    syl3anc
    syl5rbbr
    orbi12d
    mpbid
end
