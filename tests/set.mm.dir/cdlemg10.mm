include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "cbs.mm"
include "eqid.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp12l.mm"
include "simp11.mm"
include "simp21.mm"
include "simp22.mm"
include "ltrnat.mm"
include "syl3anc.mm"
include "hlatjcl.mm"
include "simp13l.mm"
include "latmcl.mm"
include "trlcl.mm"
include "syl2anc.mm"
include "latjcl.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "cdlemg10a.mm"
include "trlle.mm"
include "wb.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "lattrd.mm"

theorem cdlemg10
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
  assume cdlemg8.l: |- .<_ = ( le ` K )
  assume cdlemg8.j: |- .\/ = ( join ` K )
  assume cdlemg8.m: |- ./\ = ( meet ` K )
  assume cdlemg8.a: |- A = ( Atoms ` K )
  assume cdlemg8.h: |- H = ( LHyp ` K )
  assume cdlemg8.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg10.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T /\ P =/= Q ) /\ ( ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) =/= ( P .\/ Q ) /\ -. ( R ` F ) .<_ ( P .\/ Q ) /\ -. ( R ` G ) .<_ ( P .\/ Q ) ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ ( Q .\/ ( F ` ( G ` Q ) ) ) ) .<_ W )

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
    cP
    cQ
    c.or
    co
    #
    wne
    cF
    cR
    cfv
    #
    @18
    c.le
    wbr
    wn
    cG
    cR
    cfv
    #
    @18
    c.le
    wbr
    wn
    w3a
    #
    w3a
    #
    cK
    cbs
    cfv
    #
    cK
    c.le
    cP
    @15
    c.or
    co
    #
    cQ
    @17
    c.or
    co
    #
    c.an
    co
    #
    @19
    @20
    c.or
    co
    #
    cW
    @23
    eqid
    #
    cdlemg8.l
    @22
    @0
    cK
    clat
    wcel
    #
    @0
    @1
    @5
    @8
    @13
    @21
    simp11l
    #
    cK
    hllat
    syl
    #
    @22
    @29
    @24
    @23
    wcel
    #
    @25
    @23
    wcel
    #
    @26
    @23
    wcel
    @31
    @22
    @0
    @3
    @15
    cA
    wcel
    #
    @32
    @30
    @3
    @4
    @2
    @8
    @13
    @21
    simp12l
    #
    @22
    @2
    @10
    @14
    cA
    wcel
    #
    @34
    @2
    @5
    @8
    @13
    @21
    simp11
    #
    @9
    @10
    @11
    @12
    @21
    simp21
    #
    @22
    @2
    @11
    @3
    @36
    @37
    @9
    @10
    @11
    @12
    @21
    simp22
    #
    @35
    cA
    cP
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemg8.l
    cdlemg8.a
    cdlemg8.h
    cdlemg8.t
    ltrnat
    syl3anc
    cA
    @14
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg8.l
    cdlemg8.a
    cdlemg8.h
    cdlemg8.t
    ltrnat
    syl3anc
    cA
    @23
    c.or
    cK
    cP
    @15
    @28
    cdlemg8.j
    cdlemg8.a
    hlatjcl
    syl3anc
    @22
    @0
    @6
    @17
    cA
    wcel
    #
    @33
    @30
    @6
    @7
    @2
    @5
    @13
    @21
    simp13l
    #
    @22
    @2
    @10
    @16
    cA
    wcel
    #
    @40
    @37
    @38
    @22
    @2
    @11
    @6
    @42
    @37
    @39
    @41
    cA
    cQ
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemg8.l
    cdlemg8.a
    cdlemg8.h
    cdlemg8.t
    ltrnat
    syl3anc
    cA
    @16
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg8.l
    cdlemg8.a
    cdlemg8.h
    cdlemg8.t
    ltrnat
    syl3anc
    cA
    @23
    c.or
    cK
    cQ
    @17
    @28
    cdlemg8.j
    cdlemg8.a
    hlatjcl
    syl3anc
    @23
    cK
    c.an
    @24
    @25
    @28
    cdlemg8.m
    latmcl
    syl3anc
    @22
    @29
    @19
    @23
    wcel
    #
    @20
    @23
    wcel
    #
    @27
    @23
    wcel
    @31
    @22
    @2
    @10
    @43
    @37
    @38
    @23
    cR
    cT
    cF
    cH
    cK
    cW
    @28
    cdlemg8.h
    cdlemg8.t
    cdlemg10.r
    trlcl
    syl2anc
    #
    @22
    @2
    @11
    @44
    @37
    @39
    @23
    cR
    cT
    cG
    cH
    cK
    cW
    @28
    cdlemg8.h
    cdlemg8.t
    cdlemg10.r
    trlcl
    syl2anc
    #
    @23
    c.or
    cK
    @19
    @20
    @28
    cdlemg8.j
    latjcl
    syl3anc
    @22
    @1
    cW
    @23
    wcel
    #
    @0
    @1
    @5
    @8
    @13
    @21
    simp11r
    @23
    cH
    cK
    cW
    @28
    cdlemg8.h
    lhpbase
    syl
    #
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
    cdlemg8.l
    cdlemg8.j
    cdlemg8.m
    cdlemg8.a
    cdlemg8.h
    cdlemg8.t
    cdlemg10.r
    cdlemg10a
    @22
    @19
    cW
    c.le
    wbr
    #
    @20
    cW
    c.le
    wbr
    #
    @27
    cW
    c.le
    wbr
    #
    @22
    @2
    @10
    @49
    @37
    @38
    cR
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemg8.l
    cdlemg8.h
    cdlemg8.t
    cdlemg10.r
    trlle
    syl2anc
    @22
    @2
    @11
    @50
    @37
    @39
    cR
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemg8.l
    cdlemg8.h
    cdlemg8.t
    cdlemg10.r
    trlle
    syl2anc
    @22
    @29
    @43
    @44
    @47
    @49
    @50
    wa
    @51
    wb
    @31
    @45
    @46
    @48
    @23
    c.or
    cK
    c.le
    @19
    @20
    cW
    @28
    cdlemg8.l
    cdlemg8.j
    latjle12
    syl13anc
    mpbi2and
    lattrd
end
