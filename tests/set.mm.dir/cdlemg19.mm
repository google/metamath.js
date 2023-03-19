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
include "clat.mm"
include "cbs.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp12l.mm"
include "simp11.mm"
include "simp21.mm"
include "ltrncoat.mm"
include "syl3anc.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "simp13l.mm"
include "latmcom.mm"
include "cdlemg19a.mm"
include "simp13.mm"
include "simp12.mm"
include "simp22.mm"
include "necomd.mm"
include "simp21r.mm"
include "simp23.mm"
include "ltrnatneq.mm"
include "syl131anc.mm"
include "simp31.mm"
include "hlatjcom.mm"
include "breqtrd.mm"
include "simp32.mm"
include "3netr3d.mm"
include "simp33.mm"
include "eqcom.mm"
include "anbi2i.mm"
include "rexbii.mm"
include "sylnib.mm"
include "syl333anc.mm"
include "3eqtr3d.mm"

theorem cdlemg19
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( F e. T /\ G e. T ) /\ P =/= Q /\ ( G ` P ) =/= P ) /\ ( ( R ` G ) .<_ ( P .\/ Q ) /\ ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) =/= ( P .\/ Q ) /\ -. E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ W ) = ( ( Q .\/ ( F ` ( G ` Q ) ) ) ./\ W ) )

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
    cG
    cfv
    #
    cP
    wne
    #
    w3a
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
    @14
    cF
    cfv
    #
    cQ
    cG
    cfv
    #
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
    @25
    c.or
    co
    #
    cQ
    @25
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
    @20
    c.or
    co
    #
    cQ
    @22
    c.or
    co
    #
    c.an
    co
    #
    @36
    @35
    c.an
    co
    #
    @35
    cW
    c.an
    co
    @36
    cW
    c.an
    co
    #
    @34
    cK
    clat
    wcel
    #
    @35
    cK
    cbs
    cfv
    #
    wcel
    #
    @36
    @41
    wcel
    #
    @37
    @38
    wceq
    @34
    @0
    @40
    @0
    @1
    @5
    @8
    @16
    @33
    simp11l
    #
    cK
    hllat
    syl
    @34
    @0
    @3
    @20
    cA
    wcel
    #
    @42
    @44
    @3
    @4
    @2
    @8
    @16
    @33
    simp12l
    #
    @34
    @2
    @12
    @3
    @45
    @2
    @5
    @8
    @16
    @33
    simp11
    #
    @9
    @12
    @13
    @15
    @33
    simp21
    #
    @46
    cA
    cP
    cT
    cF
    cG
    cH
    cK
    c.le
    cW
    cdlemg12.l
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    ltrncoat
    syl3anc
    #
    cA
    @41
    c.or
    cK
    cP
    @20
    @41
    eqid
    #
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    @34
    @0
    @6
    @22
    cA
    wcel
    #
    @43
    @44
    @6
    @7
    @2
    @5
    @16
    @33
    simp13l
    #
    @34
    @2
    @12
    @6
    @51
    @47
    @48
    @52
    cA
    cQ
    cT
    cF
    cG
    cH
    cK
    c.le
    cW
    cdlemg12.l
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    ltrncoat
    syl3anc
    #
    cA
    @41
    c.or
    cK
    cQ
    @22
    @50
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    @41
    cK
    c.an
    @35
    @36
    @50
    cdlemg12.m
    latmcom
    syl3anc
    cA
    cP
    cQ
    cR
    cT
    cF
    cG
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
    cdlemg19a
    @34
    @2
    @8
    @5
    @12
    cQ
    cP
    wne
    @21
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
    @22
    @20
    c.or
    co
    #
    @55
    wne
    @26
    @28
    @27
    wceq
    #
    wa
    #
    vr
    cA
    wrex
    #
    wn
    @38
    @39
    wceq
    @47
    @2
    @5
    @8
    @16
    @33
    simp13
    #
    @2
    @5
    @8
    @16
    @33
    simp12
    #
    @48
    @34
    cP
    cQ
    @9
    @12
    @13
    @15
    @33
    simp22
    necomd
    @34
    @2
    @11
    @5
    @8
    @15
    @54
    @47
    @10
    @11
    @13
    @15
    @9
    @33
    simp21r
    @61
    @60
    @9
    @12
    @13
    @15
    @33
    simp23
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
    @34
    @17
    @18
    @55
    c.le
    @9
    @16
    @19
    @24
    @32
    simp31
    @34
    @0
    @3
    @6
    @18
    @55
    wceq
    @44
    @46
    @52
    cA
    c.or
    cK
    cP
    cQ
    cdlemg12.j
    cdlemg12.a
    hlatjcom
    syl3anc
    #
    breqtrd
    @34
    @23
    @18
    @56
    @55
    @9
    @16
    @19
    @24
    @32
    simp32
    @34
    @0
    @45
    @51
    @23
    @56
    wceq
    @44
    @49
    @53
    cA
    c.or
    cK
    @20
    @22
    cdlemg12.j
    cdlemg12.a
    hlatjcom
    syl3anc
    @62
    3netr3d
    @34
    @31
    @59
    @9
    @16
    @19
    @24
    @32
    simp33
    @30
    @58
    vr
    cA
    @29
    @57
    @26
    @27
    @28
    eqcom
    anbi2i
    rexbii
    sylnib
    cA
    cQ
    cP
    cR
    cT
    cF
    cG
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
    cdlemg19a
    syl333anc
    3eqtr3d
end
