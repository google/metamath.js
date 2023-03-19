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
include "latmle1.mm"
include "cdlemg18.mm"
include "wb.mm"
include "cdlemg18d.mm"
include "atbase.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "cal.mm"
include "hlatl.mm"
include "simp12.mm"
include "simp13.mm"
include "simp21l.mm"
include "simp21r.mm"
include "simp32.mm"
include "cdlemg11a.mm"
include "syl123anc.mm"
include "necomd.mm"
include "lhpat.mm"
include "syl112anc.mm"
include "atcmp.mm"
include "mpbid.mm"

theorem cdlemg19a
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( F e. T /\ G e. T ) /\ P =/= Q /\ ( G ` P ) =/= P ) /\ ( ( R ` G ) .<_ ( P .\/ Q ) /\ ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) =/= ( P .\/ Q ) /\ -. E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ ( Q .\/ ( F ` ( G ` Q ) ) ) ) = ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ W ) )

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
    cF
    cfv
    #
    c.or
    co
    @17
    wne
    #
    vr
    cv
    #
    cW
    c.le
    wbr
    wn
    cP
    @22
    c.or
    co
    cQ
    @22
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
    cP
    @19
    c.or
    co
    #
    cQ
    @20
    c.or
    co
    #
    c.an
    co
    #
    @26
    cW
    c.an
    co
    #
    c.le
    wbr
    #
    @28
    @29
    wceq
    #
    @25
    @28
    @26
    c.le
    wbr
    #
    @28
    cW
    c.le
    wbr
    #
    @30
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
    @35
    wcel
    #
    @32
    @25
    @0
    @34
    @0
    @1
    @5
    @8
    @16
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
    @19
    cA
    wcel
    #
    @36
    @38
    @3
    @4
    @2
    @8
    @16
    @24
    simp12l
    #
    @25
    @2
    @12
    @3
    @40
    @2
    @5
    @8
    @16
    @24
    simp11
    #
    @9
    @12
    @13
    @15
    @24
    simp21
    #
    @41
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
    @35
    c.or
    cK
    cP
    @19
    @35
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
    @20
    cA
    wcel
    #
    @37
    @38
    @6
    @7
    @2
    @5
    @16
    @24
    simp13l
    #
    @25
    @2
    @12
    @6
    @47
    @42
    @43
    @48
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
    @35
    c.or
    cK
    cQ
    @20
    @45
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    @35
    cK
    c.le
    c.an
    @26
    @27
    @45
    cdlemg12.l
    cdlemg12.m
    latmle1
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
    cdlemg18
    @25
    @34
    @28
    @35
    wcel
    #
    @36
    cW
    @35
    wcel
    #
    @32
    @33
    wa
    @30
    wb
    @39
    @25
    @28
    cA
    wcel
    #
    @49
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
    cdlemg18d
    #
    cA
    @35
    @28
    cK
    @45
    cdlemg12.a
    atbase
    syl
    @46
    @25
    @1
    @50
    @0
    @1
    @5
    @8
    @16
    @24
    simp11r
    @35
    cH
    cK
    cW
    @45
    cdlemg12.h
    lhpbase
    syl
    @35
    cK
    c.le
    c.an
    @28
    @26
    cW
    @45
    cdlemg12.l
    cdlemg12.m
    latlem12
    syl13anc
    mpbi2and
    @25
    cK
    cal
    wcel
    #
    @51
    @29
    cA
    wcel
    #
    @30
    @31
    wb
    @25
    @0
    @53
    @38
    cK
    hlatl
    syl
    @52
    @25
    @2
    @5
    @40
    cP
    @19
    wne
    @54
    @42
    @2
    @5
    @8
    @16
    @24
    simp12
    #
    @44
    @25
    @19
    cP
    @25
    @2
    @5
    @8
    @10
    @11
    @21
    @19
    cP
    wne
    @42
    @55
    @2
    @5
    @8
    @16
    @24
    simp13
    @10
    @11
    @13
    @15
    @9
    @24
    simp21l
    @10
    @11
    @13
    @15
    @9
    @24
    simp21r
    @9
    @16
    @18
    @21
    @23
    simp32
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
    syl123anc
    necomd
    cA
    cP
    @19
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
    cA
    @28
    @29
    cK
    c.le
    cdlemg12.l
    cdlemg12.a
    atcmp
    syl3anc
    mpbid
end
