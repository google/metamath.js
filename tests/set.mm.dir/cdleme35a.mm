include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp2rl.mm"
include "eqid.mm"
include "atbase.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp2r.mm"
include "simp2l.mm"
include "simp3.mm"
include "cdleme3fa.mm"
include "syl132anc.mm"
include "latlej2.mm"
include "syl3anc.mm"
include "simp12l.mm"
include "simp13l.mm"
include "cdleme1.mm"
include "syl13anc.mm"
include "breqtrd.mm"
include "cdleme0a.mm"
include "syl112anc.mm"
include "wb.mm"
include "hlatjcl.mm"
include "latjle12.mm"
include "mpbi2and.mm"
include "cdleme3g.mm"
include "ps-1.mm"
include "mpbid.mm"

theorem cdleme35a
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdleme35.l: |- .<_ = ( le ` K )
  assume cdleme35.j: |- .\/ = ( join ` K )
  assume cdleme35.m: |- ./\ = ( meet ` K )
  assume cdleme35.a: |- A = ( Atoms ` K )
  assume cdleme35.h: |- H = ( LHyp ` K )
  assume cdleme35.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme35.f: |- F = ( ( R .\/ U ) ./\ ( Q .\/ ( ( P .\/ R ) ./\ W ) ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) ) /\ -. R .<_ ( P .\/ Q ) ) -> ( F .\/ U ) = ( R .\/ U ) )

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
    cP
    cQ
    wne
    #
    cR
    cA
    wcel
    #
    cR
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    wa
    #
    cR
    cP
    cQ
    c.or
    co
    c.le
    wbr
    wn
    #
    w3a
    #
    cF
    cU
    c.or
    co
    #
    cR
    cU
    c.or
    co
    #
    c.le
    wbr
    #
    @17
    @18
    wceq
    #
    @16
    cF
    @18
    c.le
    wbr
    #
    cU
    @18
    c.le
    wbr
    #
    @19
    @16
    cF
    cR
    cF
    c.or
    co
    #
    @18
    c.le
    @16
    cK
    clat
    wcel
    #
    cR
    cK
    cbs
    cfv
    #
    wcel
    #
    cF
    @25
    wcel
    #
    cF
    @23
    c.le
    wbr
    @16
    @0
    @24
    @0
    @1
    @5
    @8
    @14
    @15
    simp11l
    #
    cK
    hllat
    syl
    #
    @16
    @11
    @26
    @11
    @12
    @10
    @9
    @15
    simp2rl
    #
    cA
    @25
    cR
    cK
    @25
    eqid
    #
    cdleme35.a
    atbase
    syl
    #
    @16
    cF
    cA
    wcel
    #
    @27
    @16
    @2
    @5
    @8
    @13
    @10
    @15
    @33
    @2
    @5
    @8
    @14
    @15
    simp11
    #
    @2
    @5
    @8
    @14
    @15
    simp12
    #
    @2
    @5
    @8
    @14
    @15
    simp13
    #
    @9
    @10
    @13
    @15
    simp2r
    #
    @9
    @10
    @13
    @15
    simp2l
    #
    @9
    @14
    @15
    simp3
    #
    cA
    cP
    cQ
    cR
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme35.l
    cdleme35.j
    cdleme35.m
    cdleme35.a
    cdleme35.h
    cdleme35.u
    cdleme35.f
    cdleme3fa
    syl132anc
    #
    cA
    @25
    cF
    cK
    @31
    cdleme35.a
    atbase
    syl
    #
    @25
    c.or
    cK
    c.le
    cR
    cF
    @31
    cdleme35.l
    cdleme35.j
    latlej2
    syl3anc
    @16
    @2
    @3
    @6
    @13
    @23
    @18
    wceq
    @34
    @3
    @4
    @2
    @8
    @14
    @15
    simp12l
    @6
    @7
    @2
    @5
    @14
    @15
    simp13l
    #
    @37
    cA
    cP
    cQ
    cR
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme35.l
    cdleme35.j
    cdleme35.m
    cdleme35.a
    cdleme35.h
    cdleme35.u
    cdleme35.f
    cdleme1
    syl13anc
    breqtrd
    @16
    @24
    @26
    cU
    @25
    wcel
    #
    @22
    @29
    @32
    @16
    cU
    cA
    wcel
    #
    @43
    @16
    @2
    @5
    @6
    @10
    @44
    @34
    @35
    @42
    @38
    cA
    cP
    cQ
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme35.l
    cdleme35.j
    cdleme35.m
    cdleme35.a
    cdleme35.h
    cdleme35.u
    cdleme0a
    syl112anc
    #
    cA
    @25
    cU
    cK
    @31
    cdleme35.a
    atbase
    syl
    #
    @25
    c.or
    cK
    c.le
    cR
    cU
    @31
    cdleme35.l
    cdleme35.j
    latlej2
    syl3anc
    @16
    @24
    @27
    @43
    @18
    @25
    wcel
    #
    @21
    @22
    wa
    @19
    wb
    @29
    @41
    @46
    @16
    @0
    @11
    @44
    @47
    @28
    @30
    @45
    cA
    @25
    c.or
    cK
    cR
    cU
    @31
    cdleme35.j
    cdleme35.a
    hlatjcl
    syl3anc
    @25
    c.or
    cK
    c.le
    cF
    cU
    @18
    @31
    cdleme35.l
    cdleme35.j
    latjle12
    syl13anc
    mpbi2and
    @16
    @0
    @33
    @44
    cF
    cU
    wne
    #
    @11
    @44
    @19
    @20
    wb
    @28
    @40
    @45
    @16
    @2
    @5
    @8
    @13
    @10
    @15
    @48
    @34
    @35
    @36
    @37
    @38
    @39
    cA
    cP
    cQ
    cR
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cP
    cR
    c.or
    co
    cW
    c.an
    co
    #
    cW
    cdleme35.l
    cdleme35.j
    cdleme35.m
    cdleme35.a
    cdleme35.h
    cdleme35.u
    cdleme35.f
    @49
    eqid
    cdleme3g
    syl132anc
    @30
    @45
    cA
    cF
    cU
    cR
    cU
    c.or
    cK
    c.le
    cdleme35.l
    cdleme35.j
    cdleme35.a
    ps-1
    syl132anc
    mpbid
end
