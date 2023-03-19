include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "simp11l.mm"
include "simp12l.mm"
include "simp2rl.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13l.mm"
include "simp2l.mm"
include "cdleme0a.mm"
include "syl112anc.mm"
include "simp12r.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "breq1.mm"
include "syl5ibcom.mm"
include "necon3bd.mm"
include "mpd.mm"
include "simp3.mm"
include "latmle1.mm"
include "hlatlej1.mm"
include "wb.mm"
include "atbase.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "wi.mm"
include "lattr.mm"
include "mpan2d.mm"
include "mtod.mm"
include "2llnma2.mm"
include "syl132anc.mm"
include "eqtrd.mm"

theorem cdleme35f
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) ) /\ -. R .<_ ( P .\/ Q ) ) -> ( ( R .\/ U ) ./\ ( P .\/ R ) ) = R )

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
    #
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
    #
    c.le
    wbr
    #
    wn
    #
    w3a
    #
    cR
    cU
    c.or
    co
    #
    cP
    cR
    c.or
    co
    #
    c.an
    co
    @20
    cR
    cP
    c.or
    co
    #
    c.an
    co
    #
    cR
    @19
    @21
    @22
    @20
    c.an
    @19
    @0
    @3
    @12
    @21
    @22
    wceq
    @0
    @1
    @6
    @9
    @15
    @18
    simp11l
    #
    @3
    @5
    @2
    @9
    @15
    @18
    simp12l
    #
    @12
    @13
    @11
    @10
    @18
    simp2rl
    #
    cA
    c.or
    cK
    cP
    cR
    cdleme35.j
    cdleme35.a
    hlatjcom
    syl3anc
    oveq2d
    @19
    @0
    cU
    cA
    wcel
    #
    @3
    @12
    cU
    cP
    wne
    #
    cR
    cU
    cP
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    @23
    cR
    wceq
    @24
    @19
    @2
    @6
    @7
    @11
    @27
    @2
    @6
    @9
    @15
    @18
    simp11
    @2
    @6
    @9
    @15
    @18
    simp12
    @7
    @8
    @2
    @6
    @15
    @18
    simp13l
    #
    @10
    @11
    @14
    @18
    simp2l
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
    @25
    @26
    @19
    @5
    @28
    @3
    @5
    @2
    @9
    @15
    @18
    simp12r
    @19
    @4
    cU
    cP
    @19
    cU
    cW
    c.le
    wbr
    cU
    cP
    wceq
    @4
    @19
    cU
    @16
    cW
    c.an
    co
    #
    cW
    c.le
    cdleme35.u
    @19
    cK
    clat
    wcel
    #
    @16
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @35
    wcel
    #
    @33
    cW
    c.le
    wbr
    @19
    @0
    @34
    @24
    cK
    hllat
    syl
    #
    @19
    @0
    @3
    @7
    @36
    @24
    @25
    @31
    cA
    @35
    c.or
    cK
    cP
    cQ
    @35
    eqid
    #
    cdleme35.j
    cdleme35.a
    hlatjcl
    syl3anc
    #
    @19
    @1
    @37
    @0
    @1
    @6
    @9
    @15
    @18
    simp11r
    @35
    cH
    cK
    cW
    @39
    cdleme35.h
    lhpbase
    syl
    #
    @35
    cK
    c.le
    c.an
    @16
    cW
    @39
    cdleme35.l
    cdleme35.m
    latmle2
    syl3anc
    syl5eqbr
    cU
    cP
    cW
    c.le
    breq1
    syl5ibcom
    necon3bd
    mpd
    @19
    @30
    @17
    @10
    @15
    @18
    simp3
    @19
    @30
    @29
    @16
    c.le
    wbr
    #
    @17
    @19
    cU
    @16
    c.le
    wbr
    #
    cP
    @16
    c.le
    wbr
    #
    @42
    @19
    cU
    @33
    @16
    c.le
    cdleme35.u
    @19
    @34
    @36
    @37
    @33
    @16
    c.le
    wbr
    @38
    @40
    @41
    @35
    cK
    c.le
    c.an
    @16
    cW
    @39
    cdleme35.l
    cdleme35.m
    latmle1
    syl3anc
    syl5eqbr
    @19
    @0
    @3
    @7
    @44
    @24
    @25
    @31
    cA
    cP
    cQ
    c.or
    cK
    c.le
    cdleme35.l
    cdleme35.j
    cdleme35.a
    hlatlej1
    syl3anc
    @19
    @34
    cU
    @35
    wcel
    #
    cP
    @35
    wcel
    #
    @36
    @43
    @44
    wa
    @42
    wb
    @38
    @19
    @27
    @45
    @32
    cA
    @35
    cU
    cK
    @39
    cdleme35.a
    atbase
    syl
    @19
    @3
    @46
    @25
    cA
    @35
    cP
    cK
    @39
    cdleme35.a
    atbase
    syl
    @40
    @35
    c.or
    cK
    c.le
    cU
    cP
    @16
    @39
    cdleme35.l
    cdleme35.j
    latjle12
    syl13anc
    mpbi2and
    @19
    @34
    cR
    @35
    wcel
    #
    @29
    @35
    wcel
    #
    @36
    @30
    @42
    wa
    @17
    wi
    @38
    @19
    @12
    @47
    @26
    cA
    @35
    cR
    cK
    @39
    cdleme35.a
    atbase
    syl
    @19
    @0
    @27
    @3
    @48
    @24
    @32
    @25
    cA
    @35
    c.or
    cK
    cU
    cP
    @39
    cdleme35.j
    cdleme35.a
    hlatjcl
    syl3anc
    @40
    @35
    cK
    c.le
    cR
    @29
    @16
    @39
    cdleme35.l
    lattr
    syl13anc
    mpan2d
    mtod
    cA
    cU
    cP
    cR
    c.or
    cK
    c.le
    c.an
    cdleme35.l
    cdleme35.j
    cdleme35.m
    cdleme35.a
    2llnma2
    syl132anc
    eqtrd
end
