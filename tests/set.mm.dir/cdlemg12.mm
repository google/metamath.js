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
include "wceq.mm"
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
include "latmcom.mm"
include "cdlemg12g.mm"
include "simp13.mm"
include "simp12.mm"
include "simp23.mm"
include "necomd.mm"
include "simp31l.mm"
include "hlatjcom.mm"
include "breq2d.mm"
include "mtbid.mm"
include "simp31r.mm"
include "jca.mm"
include "simp32.mm"
include "simp33.mm"
include "3netr3d.mm"
include "syl333anc.mm"
include "3eqtr3d.mm"

theorem cdlemg12
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T /\ P =/= Q ) /\ ( ( -. ( R ` F ) .<_ ( P .\/ Q ) /\ -. ( R ` G ) .<_ ( P .\/ Q ) ) /\ ( R ` F ) =/= ( R ` G ) /\ ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) =/= ( P .\/ Q ) ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ W ) = ( ( Q .\/ ( F ` ( G ` Q ) ) ) ./\ W ) )

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
    #
    wn
    #
    cG
    cR
    cfv
    #
    @15
    c.le
    wbr
    #
    wn
    #
    wa
    #
    @14
    @18
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
    #
    @15
    wne
    #
    w3a
    #
    w3a
    #
    cP
    @23
    c.or
    co
    #
    cQ
    @24
    c.or
    co
    #
    c.an
    co
    #
    @30
    @29
    c.an
    co
    #
    @29
    cW
    c.an
    co
    @30
    cW
    c.an
    co
    #
    @28
    cK
    clat
    wcel
    #
    @29
    cK
    cbs
    cfv
    #
    wcel
    #
    @30
    @35
    wcel
    #
    @31
    @32
    wceq
    @28
    @0
    @34
    @0
    @1
    @5
    @8
    @13
    @27
    simp11l
    #
    cK
    hllat
    syl
    @28
    @0
    @3
    @23
    cA
    wcel
    #
    @36
    @38
    @3
    @4
    @2
    @8
    @13
    @27
    simp12l
    #
    @28
    @2
    @10
    @11
    @3
    @39
    @2
    @5
    @8
    @13
    @27
    simp11
    #
    @9
    @10
    @11
    @12
    @27
    simp21
    #
    @9
    @10
    @11
    @12
    @27
    simp22
    #
    @40
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
    #
    cA
    @35
    c.or
    cK
    cP
    @23
    @35
    eqid
    #
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    @28
    @0
    @6
    @24
    cA
    wcel
    #
    @37
    @38
    @6
    @7
    @2
    @5
    @13
    @27
    simp13l
    #
    @28
    @2
    @10
    @11
    @6
    @46
    @41
    @42
    @43
    @47
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
    #
    cA
    @35
    c.or
    cK
    cQ
    @24
    @45
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    @35
    cK
    c.an
    @29
    @30
    @45
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
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg12g
    @28
    @2
    @8
    @5
    @10
    @11
    cQ
    cP
    wne
    @14
    cQ
    cP
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    @18
    @49
    c.le
    wbr
    #
    wn
    #
    wa
    @22
    @24
    @23
    c.or
    co
    #
    @49
    wne
    @32
    @33
    wceq
    @41
    @2
    @5
    @8
    @13
    @27
    simp13
    @2
    @5
    @8
    @13
    @27
    simp12
    @42
    @43
    @28
    cP
    cQ
    @9
    @10
    @11
    @12
    @27
    simp23
    necomd
    @28
    @51
    @53
    @28
    @16
    @50
    @17
    @20
    @22
    @26
    @9
    @13
    simp31l
    @28
    @15
    @49
    @14
    c.le
    @28
    @0
    @3
    @6
    @15
    @49
    wceq
    @38
    @40
    @47
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
    breq2d
    mtbid
    @28
    @19
    @52
    @17
    @20
    @22
    @26
    @9
    @13
    simp31r
    @28
    @15
    @49
    @18
    c.le
    @55
    breq2d
    mtbid
    jca
    @9
    @13
    @21
    @22
    @26
    simp32
    @28
    @25
    @15
    @54
    @49
    @9
    @13
    @21
    @22
    @26
    simp33
    @28
    @0
    @39
    @46
    @25
    @54
    wceq
    @38
    @44
    @48
    cA
    c.or
    cK
    @23
    @24
    cdlemg12.j
    cdlemg12.a
    hlatjcom
    syl3anc
    @55
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
    cdlemg12g
    syl333anc
    3eqtr3d
end
