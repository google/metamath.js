include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "clat.mm"
include "cbs.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp12l.mm"
include "simp11.mm"
include "simp21.mm"
include "simp22.mm"
include "ltrncoat.mm"
include "syl121anc.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp13l.mm"
include "latmle1.mm"
include "simp1.mm"
include "simp2.mm"
include "simp33.mm"
include "simp31l.mm"
include "simp31r.mm"
include "cdlemg10.mm"
include "syl113anc.mm"
include "wb.mm"
include "latmcl.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"

theorem cdlemg12f
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T /\ P =/= Q ) /\ ( ( -. ( R ` F ) .<_ ( P .\/ Q ) /\ -. ( R ` G ) .<_ ( P .\/ Q ) ) /\ ( R ` F ) =/= ( R ` G ) /\ ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) =/= ( P .\/ Q ) ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ ( Q .\/ ( F ` ( G ` Q ) ) ) ) .<_ ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ W ) )

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
    wn
    #
    cG
    cR
    cfv
    #
    @15
    c.le
    wbr
    wn
    #
    wa
    #
    @14
    @17
    wne
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
    @15
    wne
    #
    w3a
    #
    w3a
    #
    cP
    @21
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
    @26
    c.le
    wbr
    #
    @28
    cW
    c.le
    wbr
    #
    @28
    @26
    cW
    c.an
    co
    c.le
    wbr
    #
    @25
    cK
    clat
    wcel
    #
    @26
    cK
    cbs
    cfv
    #
    wcel
    #
    @27
    @33
    wcel
    #
    @29
    @25
    @0
    @32
    @0
    @1
    @5
    @8
    @13
    @24
    simp11l
    #
    cK
    hllat
    syl
    #
    @25
    @0
    @3
    @21
    cA
    wcel
    #
    @34
    @36
    @3
    @4
    @2
    @8
    @13
    @24
    simp12l
    #
    @25
    @2
    @10
    @11
    @3
    @38
    @2
    @5
    @8
    @13
    @24
    simp11
    #
    @9
    @10
    @11
    @12
    @24
    simp21
    #
    @9
    @10
    @11
    @12
    @24
    simp22
    #
    @39
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
    syl121anc
    cA
    @33
    c.or
    cK
    cP
    @21
    @33
    eqid
    #
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    #
    @25
    @0
    @6
    @22
    cA
    wcel
    #
    @35
    @36
    @6
    @7
    @2
    @5
    @13
    @24
    simp13l
    #
    @25
    @2
    @10
    @11
    @6
    @45
    @40
    @41
    @42
    @46
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
    syl121anc
    cA
    @33
    c.or
    cK
    cQ
    @22
    @43
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    #
    @33
    cK
    c.le
    c.an
    @26
    @27
    @43
    cdlemg12.l
    cdlemg12.m
    latmle1
    syl3anc
    @25
    @9
    @13
    @23
    @16
    @18
    @30
    @9
    @13
    @24
    simp1
    @9
    @13
    @24
    simp2
    @9
    @13
    @19
    @20
    @23
    simp33
    @16
    @18
    @20
    @23
    @9
    @13
    simp31l
    @16
    @18
    @20
    @23
    @9
    @13
    simp31r
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
    cdlemg10
    syl113anc
    @25
    @32
    @28
    @33
    wcel
    #
    @34
    cW
    @33
    wcel
    #
    @29
    @30
    wa
    @31
    wb
    @37
    @25
    @32
    @34
    @35
    @48
    @37
    @44
    @47
    @33
    cK
    c.an
    @26
    @27
    @43
    cdlemg12.m
    latmcl
    syl3anc
    @44
    @25
    @1
    @49
    @0
    @1
    @5
    @8
    @13
    @24
    simp11r
    @33
    cH
    cK
    cW
    @43
    cdlemg12.h
    lhpbase
    syl
    @33
    cK
    c.le
    c.an
    @28
    @26
    cW
    @43
    cdlemg12.l
    cdlemg12.m
    latlem12
    syl13anc
    mpbi2and
end
