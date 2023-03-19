include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "cdleme1.mm"
include "oveq1d.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "simpll.mm"
include "simpr3l.mm"
include "clat.mm"
include "hllat.mm"
include "ad2antrr.mm"
include "simpr1.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simpr2.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "lhpbase.mm"
include "ad2antlr.mm"
include "latmcl.mm"
include "syl5eqel.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "atmod4i2.mm"
include "syl131anc.mm"
include "cp0.mm"
include "lhpmat.mm"
include "3ad2antr3.mm"
include "col.mm"
include "hlol.mm"
include "olj02.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "3eqtr2d.mm"

theorem cdleme2
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
  assume cdleme1.l: |- .<_ = ( le ` K )
  assume cdleme1.j: |- .\/ = ( join ` K )
  assume cdleme1.m: |- ./\ = ( meet ` K )
  assume cdleme1.a: |- A = ( Atoms ` K )
  assume cdleme1.h: |- H = ( LHyp ` K )
  assume cdleme1.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme1.f: |- F = ( ( R .\/ U ) ./\ ( Q .\/ ( ( P .\/ R ) ./\ W ) ) )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ Q e. A /\ ( R e. A /\ -. R .<_ W ) ) ) -> ( ( R .\/ F ) ./\ W ) = U )

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
    cQ
    cA
    wcel
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
    w3a
    #
    wa
    #
    cR
    cF
    c.or
    co
    #
    cW
    c.an
    co
    cR
    cU
    c.or
    co
    #
    cW
    c.an
    co
    #
    cR
    cW
    c.an
    co
    #
    cU
    c.or
    co
    #
    cU
    @9
    @10
    @11
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
    cdleme1.l
    cdleme1.j
    cdleme1.m
    cdleme1.a
    cdleme1.h
    cdleme1.u
    cdleme1.f
    cdleme1
    oveq1d
    @9
    @0
    @5
    cU
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @15
    wcel
    #
    cU
    cW
    c.le
    wbr
    @14
    @12
    wceq
    @0
    @1
    @8
    simpll
    @5
    @6
    @3
    @4
    @2
    simpr3l
    @9
    cU
    cP
    cQ
    c.or
    co
    #
    cW
    c.an
    co
    #
    @15
    cdleme1.u
    @9
    cK
    clat
    wcel
    #
    @18
    @15
    wcel
    #
    @17
    @19
    @15
    wcel
    @0
    @20
    @1
    @8
    cK
    hllat
    ad2antrr
    #
    @9
    @20
    cP
    @15
    wcel
    #
    cQ
    @15
    wcel
    #
    @21
    @22
    @9
    @3
    @23
    @2
    @3
    @4
    @7
    simpr1
    cA
    @15
    cP
    cK
    @15
    eqid
    #
    cdleme1.a
    atbase
    syl
    @9
    @4
    @24
    @2
    @3
    @4
    @7
    simpr2
    cA
    @15
    cQ
    cK
    @25
    cdleme1.a
    atbase
    syl
    @15
    c.or
    cK
    cP
    cQ
    @25
    cdleme1.j
    latjcl
    syl3anc
    #
    @1
    @17
    @0
    @8
    @15
    cH
    cK
    cW
    @25
    cdleme1.h
    lhpbase
    ad2antlr
    #
    @15
    cK
    c.an
    @18
    cW
    @25
    cdleme1.m
    latmcl
    syl3anc
    syl5eqel
    #
    @27
    @9
    cU
    @19
    cW
    c.le
    cdleme1.u
    @9
    @20
    @21
    @17
    @19
    cW
    c.le
    wbr
    @22
    @26
    @27
    @15
    cK
    c.le
    c.an
    @18
    cW
    @25
    cdleme1.l
    cdleme1.m
    latmle2
    syl3anc
    syl5eqbr
    cA
    @15
    cR
    c.or
    cK
    c.le
    c.an
    cU
    cW
    @25
    cdleme1.l
    cdleme1.j
    cdleme1.m
    cdleme1.a
    atmod4i2
    syl131anc
    @9
    @14
    cK
    cp0
    cfv
    #
    cU
    c.or
    co
    #
    cU
    @9
    @13
    @29
    cU
    c.or
    @2
    @3
    @7
    @13
    @29
    wceq
    @4
    cA
    cR
    cH
    cK
    c.le
    c.an
    cW
    @29
    cdleme1.l
    cdleme1.m
    @29
    eqid
    #
    cdleme1.a
    cdleme1.h
    lhpmat
    3ad2antr3
    oveq1d
    @9
    cK
    col
    wcel
    #
    @16
    @30
    cU
    wceq
    @0
    @32
    @1
    @8
    cK
    hlol
    ad2antrr
    @28
    @15
    c.or
    cK
    cU
    @29
    @25
    cdleme1.j
    @31
    olj02
    syl2anc
    eqtrd
    3eqtr2d
end
