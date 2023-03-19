include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cdleme35c.mm"
include "oveq1d.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "simp11l.mm"
include "simp13l.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "simp12l.mm"
include "simp2rl.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "latmle2.mm"
include "atmod4i2.mm"
include "syl131anc.mm"
include "cp0.mm"
include "simp11.mm"
include "simp13.mm"
include "lhpmat.mm"
include "syl2anc.mm"
include "col.mm"
include "hlol.mm"
include "olj02.mm"
include "eqtrd.mm"
include "3eqtr2d.mm"

theorem cdleme35d
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) ) /\ -. R .<_ ( P .\/ Q ) ) -> ( ( Q .\/ F ) ./\ W ) = ( ( P .\/ R ) ./\ W ) )

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
    #
    cW
    c.an
    co
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
    cW
    c.an
    co
    #
    cQ
    cW
    c.an
    co
    #
    @18
    c.or
    co
    #
    @18
    @15
    @16
    @19
    cW
    c.an
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
    cdleme35c
    oveq1d
    @15
    @0
    @6
    @18
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @23
    wcel
    #
    @18
    cW
    c.le
    wbr
    #
    @22
    @20
    wceq
    @0
    @1
    @5
    @8
    @13
    @14
    simp11l
    #
    @6
    @7
    @2
    @5
    @13
    @14
    simp13l
    @15
    cK
    clat
    wcel
    #
    @17
    @23
    wcel
    #
    @25
    @24
    @15
    @0
    @28
    @27
    cK
    hllat
    syl
    #
    @15
    @0
    @3
    @11
    @29
    @27
    @3
    @4
    @2
    @8
    @13
    @14
    simp12l
    @11
    @12
    @10
    @9
    @14
    simp2rl
    cA
    @23
    c.or
    cK
    cP
    cR
    @23
    eqid
    #
    cdleme35.j
    cdleme35.a
    hlatjcl
    syl3anc
    #
    @15
    @1
    @25
    @0
    @1
    @5
    @8
    @13
    @14
    simp11r
    @23
    cH
    cK
    cW
    @31
    cdleme35.h
    lhpbase
    syl
    #
    @23
    cK
    c.an
    @17
    cW
    @31
    cdleme35.m
    latmcl
    syl3anc
    #
    @33
    @15
    @28
    @29
    @25
    @26
    @30
    @32
    @33
    @23
    cK
    c.le
    c.an
    @17
    cW
    @31
    cdleme35.l
    cdleme35.m
    latmle2
    syl3anc
    cA
    @23
    cQ
    c.or
    cK
    c.le
    c.an
    @18
    cW
    @31
    cdleme35.l
    cdleme35.j
    cdleme35.m
    cdleme35.a
    atmod4i2
    syl131anc
    @15
    @22
    cK
    cp0
    cfv
    #
    @18
    c.or
    co
    #
    @18
    @15
    @21
    @35
    @18
    c.or
    @15
    @2
    @8
    @21
    @35
    wceq
    @2
    @5
    @8
    @13
    @14
    simp11
    @2
    @5
    @8
    @13
    @14
    simp13
    cA
    cQ
    cH
    cK
    c.le
    c.an
    cW
    @35
    cdleme35.l
    cdleme35.m
    @35
    eqid
    #
    cdleme35.a
    cdleme35.h
    lhpmat
    syl2anc
    oveq1d
    @15
    cK
    col
    wcel
    #
    @24
    @36
    @18
    wceq
    @15
    @0
    @38
    @27
    cK
    hlol
    syl
    @34
    @23
    c.or
    cK
    @18
    @35
    @31
    cdleme35.j
    @37
    olj02
    syl2anc
    eqtrd
    3eqtr2d
end
