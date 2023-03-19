include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "cops.mm"
include "cbs.mm"
include "cp0.mm"
include "wceq.mm"
include "simp11l.mm"
include "hlop.mm"
include "syl.mm"
include "clat.mm"
include "hllat.mm"
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
include "latmcl.mm"
include "simp12.mm"
include "simp13.mm"
include "simp33.mm"
include "cdlemg11a.mm"
include "necomd.mm"
include "syl123anc.mm"
include "lhpat.mm"
include "syl112anc.mm"
include "hlatjcom.mm"
include "oveq12d.mm"
include "simp1.mm"
include "simp2.mm"
include "simp31l.mm"
include "simp31r.mm"
include "simp32.mm"
include "cdlemg12e.mm"
include "syl113anc.mm"
include "eqnetrd.mm"
include "cdlemg12f.mm"
include "leat2.mm"
include "syl32anc.mm"

theorem cdlemg12g
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T /\ P =/= Q ) /\ ( ( -. ( R ` F ) .<_ ( P .\/ Q ) /\ -. ( R ` G ) .<_ ( P .\/ Q ) ) /\ ( R ` F ) =/= ( R ` G ) /\ ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) =/= ( P .\/ Q ) ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ ( Q .\/ ( F ` ( G ` Q ) ) ) ) = ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ W ) )

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
    cK
    cops
    wcel
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
    cK
    cbs
    cfv
    #
    wcel
    #
    @27
    cW
    c.an
    co
    #
    cA
    wcel
    #
    @29
    cK
    cp0
    cfv
    #
    wne
    @29
    @32
    c.le
    wbr
    @29
    @32
    wceq
    @25
    @0
    @26
    @0
    @1
    @5
    @8
    @13
    @24
    simp11l
    #
    cK
    hlop
    syl
    @25
    cK
    clat
    wcel
    #
    @27
    @30
    wcel
    #
    @28
    @30
    wcel
    #
    @31
    @25
    @0
    @36
    @35
    cK
    hllat
    syl
    @25
    @0
    @3
    @21
    cA
    wcel
    #
    @37
    @35
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
    @39
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
    @30
    c.or
    cK
    cP
    @21
    @30
    eqid
    #
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    @25
    @0
    @6
    @22
    cA
    wcel
    #
    @38
    @35
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
    @30
    c.or
    cK
    cQ
    @22
    @45
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    @30
    cK
    c.an
    @27
    @28
    @45
    cdlemg12.m
    latmcl
    syl3anc
    @25
    @2
    @5
    @39
    cP
    @21
    wne
    #
    @33
    @41
    @2
    @5
    @8
    @13
    @24
    simp12
    #
    @44
    @25
    @2
    @5
    @8
    @10
    @11
    @23
    @49
    @41
    @50
    @2
    @5
    @8
    @13
    @24
    simp13
    @42
    @43
    @9
    @13
    @19
    @20
    @23
    simp33
    @2
    @5
    @8
    wa
    @10
    @11
    @23
    w3a
    w3a
    @21
    cP
    cA
    cP
    cQ
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
    cdlemg11a
    necomd
    syl123anc
    cA
    cP
    @21
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
    lhpat
    syl112anc
    @25
    @29
    @21
    cP
    c.or
    co
    #
    @22
    cQ
    c.or
    co
    #
    c.an
    co
    #
    @34
    @25
    @27
    @51
    @28
    @52
    c.an
    @25
    @0
    @3
    @39
    @27
    @51
    wceq
    @35
    @40
    @44
    cA
    c.or
    cK
    cP
    @21
    cdlemg12.j
    cdlemg12.a
    hlatjcom
    syl3anc
    @25
    @0
    @6
    @46
    @28
    @52
    wceq
    @35
    @47
    @48
    cA
    c.or
    cK
    cQ
    @22
    cdlemg12.j
    cdlemg12.a
    hlatjcom
    syl3anc
    oveq12d
    @25
    @9
    @13
    @16
    @18
    @20
    @53
    @34
    wne
    @9
    @13
    @24
    simp1
    @9
    @13
    @24
    simp2
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
    @9
    @13
    @19
    @20
    @23
    simp32
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
    @34
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    @34
    eqid
    #
    cdlemg12e
    syl113anc
    eqnetrd
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
    cdlemg12f
    cA
    @30
    @32
    cK
    c.le
    @29
    @34
    @45
    cdlemg12.l
    @54
    cdlemg12.a
    leat2
    syl32anc
end
