include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "oveq2i.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "simp11l.mm"
include "simp13l.mm"
include "simp2rl.mm"
include "simp11.mm"
include "simp12.mm"
include "simp2l.mm"
include "cdleme0a.mm"
include "syl112anc.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "atbase.mm"
include "simp12l.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "latjcl.mm"
include "latlej1.mm"
include "atmod1i1.mm"
include "syl131anc.mm"
include "cdleme35b.mm"
include "wb.mm"
include "latleeqm2.mm"
include "mpbid.mm"
include "eqtrd.mm"
include "syl5eq.mm"

theorem cdleme35c
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) ) /\ -. R .<_ ( P .\/ Q ) ) -> ( Q .\/ F ) = ( Q .\/ ( ( P .\/ R ) ./\ W ) ) )

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
    cQ
    cF
    c.or
    co
    cQ
    cR
    cU
    c.or
    co
    #
    cQ
    cP
    cR
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    #
    c.or
    co
    #
    @20
    cF
    @21
    cQ
    c.or
    cdleme35.f
    oveq2i
    @16
    @22
    cQ
    @17
    c.or
    co
    #
    @20
    c.an
    co
    #
    @20
    @16
    @0
    @6
    @17
    cK
    cbs
    cfv
    #
    wcel
    #
    @20
    @25
    wcel
    #
    cQ
    @20
    c.le
    wbr
    #
    @22
    @24
    wceq
    @0
    @1
    @5
    @8
    @14
    @15
    simp11l
    #
    @6
    @7
    @2
    @5
    @14
    @15
    simp13l
    #
    @16
    @0
    @11
    cU
    cA
    wcel
    #
    @26
    @29
    @11
    @12
    @10
    @9
    @15
    simp2rl
    #
    @16
    @2
    @5
    @6
    @10
    @31
    @2
    @5
    @8
    @14
    @15
    simp11
    @2
    @5
    @8
    @14
    @15
    simp12
    @30
    @9
    @10
    @13
    @15
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
    cA
    @25
    c.or
    cK
    cR
    cU
    @25
    eqid
    #
    cdleme35.j
    cdleme35.a
    hlatjcl
    syl3anc
    #
    @16
    cK
    clat
    wcel
    #
    cQ
    @25
    wcel
    #
    @19
    @25
    wcel
    #
    @27
    @16
    @0
    @35
    @29
    cK
    hllat
    syl
    #
    @16
    @6
    @36
    @30
    cA
    @25
    cQ
    cK
    @33
    cdleme35.a
    atbase
    syl
    #
    @16
    @35
    @18
    @25
    wcel
    #
    cW
    @25
    wcel
    #
    @37
    @38
    @16
    @0
    @3
    @11
    @40
    @29
    @3
    @4
    @2
    @8
    @14
    @15
    simp12l
    @32
    cA
    @25
    c.or
    cK
    cP
    cR
    @33
    cdleme35.j
    cdleme35.a
    hlatjcl
    syl3anc
    @16
    @1
    @41
    @0
    @1
    @5
    @8
    @14
    @15
    simp11r
    @25
    cH
    cK
    cW
    @33
    cdleme35.h
    lhpbase
    syl
    @25
    cK
    c.an
    @18
    cW
    @33
    cdleme35.m
    latmcl
    syl3anc
    #
    @25
    c.or
    cK
    cQ
    @19
    @33
    cdleme35.j
    latjcl
    syl3anc
    #
    @16
    @35
    @36
    @37
    @28
    @38
    @39
    @42
    @25
    c.or
    cK
    c.le
    cQ
    @19
    @33
    cdleme35.l
    cdleme35.j
    latlej1
    syl3anc
    cA
    @25
    cQ
    c.or
    cK
    c.le
    c.an
    @17
    @20
    @33
    cdleme35.l
    cdleme35.j
    cdleme35.m
    cdleme35.a
    atmod1i1
    syl131anc
    @16
    @20
    @23
    c.le
    wbr
    #
    @24
    @20
    wceq
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
    cdleme35b
    @16
    @35
    @27
    @23
    @25
    wcel
    #
    @44
    @45
    wb
    @38
    @43
    @16
    @35
    @36
    @26
    @46
    @38
    @39
    @34
    @25
    c.or
    cK
    cQ
    @17
    @33
    cdleme35.j
    latjcl
    syl3anc
    @25
    cK
    c.le
    c.an
    @20
    @23
    @33
    cdleme35.l
    cdleme35.m
    latleeqm2
    syl3anc
    mpbid
    eqtrd
    syl5eq
end
