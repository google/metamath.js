include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "wne.mm"
include "wceq.mm"
include "co.mm"
include "simp11.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp12.mm"
include "ltrnel.mm"
include "syl3anc.mm"
include "trlval2.mm"
include "simp13.mm"
include "eqtr3d.mm"
include "cdlemg13a.mm"
include "oveq1d.mm"
include "simp2.mm"
include "simp31.mm"
include "ltrnatneq.mm"
include "syl131anc.mm"
include "simp32.mm"
include "simp33.mm"
include "simp11l.mm"
include "simp12l.mm"
include "ltrncoat.mm"
include "simp13l.mm"
include "hlatjcom.mm"
include "3netr3d.mm"
include "syl313anc.mm"
include "3eqtr4d.mm"

theorem cdlemg13
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
  assume cdlemg12.l: |- .<_ = ( le ` K )
  assume cdlemg12.j: |- .\/ = ( join ` K )
  assume cdlemg12.m: |- ./\ = ( meet ` K )
  assume cdlemg12.a: |- A = ( Atoms ` K )
  assume cdlemg12.h: |- H = ( LHyp ` K )
  assume cdlemg12.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg12b.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T ) /\ ( ( F ` P ) =/= P /\ ( R ` F ) = ( R ` G ) /\ ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) =/= ( P .\/ Q ) ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ W ) = ( ( Q .\/ ( F ` ( G ` Q ) ) ) ./\ W ) )

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
    cF
    cfv
    cP
    wne
    #
    cF
    cR
    cfv
    #
    cG
    cR
    cfv
    wceq
    #
    cP
    cG
    cfv
    #
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
    cP
    cQ
    c.or
    co
    #
    wne
    #
    w3a
    #
    w3a
    #
    @16
    @17
    c.or
    co
    #
    cW
    c.an
    co
    #
    @18
    @19
    c.or
    co
    #
    cW
    c.an
    co
    #
    cP
    @17
    c.or
    co
    #
    cW
    c.an
    co
    cQ
    @19
    c.or
    co
    #
    cW
    c.an
    co
    @24
    @14
    @26
    @28
    @24
    @2
    @10
    @16
    cA
    wcel
    @16
    cW
    c.le
    wbr
    wn
    wa
    #
    @14
    @26
    wceq
    @2
    @5
    @8
    @12
    @23
    simp11
    #
    @9
    @10
    @11
    @23
    simp2l
    #
    @24
    @2
    @11
    @5
    @31
    @32
    @9
    @10
    @11
    @23
    simp2r
    #
    @2
    @5
    @8
    @12
    @23
    simp12
    #
    cA
    cP
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
    ltrnel
    syl3anc
    cA
    @16
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    trlval2
    syl3anc
    @24
    @2
    @10
    @18
    cA
    wcel
    @18
    cW
    c.le
    wbr
    wn
    wa
    #
    @14
    @28
    wceq
    @32
    @33
    @24
    @2
    @11
    @8
    @36
    @32
    @34
    @2
    @5
    @8
    @12
    @23
    simp13
    #
    cA
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
    ltrnel
    syl3anc
    cA
    @18
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    trlval2
    syl3anc
    eqtr3d
    @24
    @29
    @25
    cW
    c.an
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
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg13a
    oveq1d
    @24
    @30
    @27
    cW
    c.an
    @24
    @2
    @8
    @5
    @12
    cQ
    cF
    cfv
    cQ
    wne
    #
    @15
    @19
    @17
    c.or
    co
    #
    cQ
    cP
    c.or
    co
    #
    wne
    @30
    @27
    wceq
    @32
    @37
    @35
    @9
    @12
    @23
    simp2
    #
    @24
    @2
    @10
    @5
    @8
    @13
    @38
    @32
    @33
    @35
    @37
    @9
    @12
    @13
    @15
    @22
    simp31
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
    @9
    @12
    @13
    @15
    @22
    simp32
    @24
    @20
    @21
    @39
    @40
    @9
    @12
    @13
    @15
    @22
    simp33
    @24
    @0
    @17
    cA
    wcel
    #
    @19
    cA
    wcel
    #
    @20
    @39
    wceq
    @0
    @1
    @5
    @8
    @12
    @23
    simp11l
    #
    @24
    @2
    @12
    @3
    @42
    @32
    @41
    @3
    @4
    @2
    @8
    @12
    @23
    simp12l
    #
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
    @24
    @2
    @12
    @6
    @43
    @32
    @41
    @6
    @7
    @2
    @5
    @12
    @23
    simp13l
    #
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
    cA
    c.or
    cK
    @17
    @19
    cdlemg12.j
    cdlemg12.a
    hlatjcom
    syl3anc
    @24
    @0
    @3
    @6
    @21
    @40
    wceq
    @44
    @45
    @46
    cA
    c.or
    cK
    cP
    cQ
    cdlemg12.j
    cdlemg12.a
    hlatjcom
    syl3anc
    3netr3d
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
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg13a
    syl313anc
    oveq1d
    3eqtr4d
end
