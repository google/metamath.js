include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cdleme35d.mm"
include "oveq2d.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "simp11l.mm"
include "simp12l.mm"
include "simp2rl.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "syl.mm"
include "hlatlej1.mm"
include "atmod3i1.mm"
include "syl131anc.mm"
include "cp1.mm"
include "simp11.mm"
include "simp12.mm"
include "lhpjat2.mm"
include "syl2anc.mm"
include "col.mm"
include "hlol.mm"
include "olm11.mm"
include "eqtrd.mm"
include "3eqtrd.mm"

theorem cdleme35e
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) ) /\ -. R .<_ ( P .\/ Q ) ) -> ( P .\/ ( ( Q .\/ F ) ./\ W ) ) = ( P .\/ R ) )

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
    cQ
    cW
    c.le
    wbr
    wn
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
    cP
    cQ
    cF
    c.or
    co
    cW
    c.an
    co
    #
    c.or
    co
    cP
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
    @15
    cP
    cW
    c.or
    co
    #
    c.an
    co
    #
    @15
    @13
    @14
    @16
    cP
    c.or
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
    cdleme35d
    oveq2d
    @13
    @0
    @3
    @15
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @20
    wcel
    #
    cP
    @15
    c.le
    wbr
    #
    @17
    @19
    wceq
    @0
    @1
    @5
    @6
    @11
    @12
    simp11l
    #
    @3
    @4
    @2
    @6
    @11
    @12
    simp12l
    #
    @13
    @0
    @3
    @9
    @21
    @24
    @25
    @9
    @10
    @8
    @7
    @12
    simp2rl
    #
    cA
    @20
    c.or
    cK
    cP
    cR
    @20
    eqid
    #
    cdleme35.j
    cdleme35.a
    hlatjcl
    syl3anc
    #
    @13
    @1
    @22
    @0
    @1
    @5
    @6
    @11
    @12
    simp11r
    @20
    cH
    cK
    cW
    @27
    cdleme35.h
    lhpbase
    syl
    @13
    @0
    @3
    @9
    @23
    @24
    @25
    @26
    cA
    cP
    cR
    c.or
    cK
    c.le
    cdleme35.l
    cdleme35.j
    cdleme35.a
    hlatlej1
    syl3anc
    cA
    @20
    cP
    c.or
    cK
    c.le
    c.an
    @15
    cW
    @27
    cdleme35.l
    cdleme35.j
    cdleme35.m
    cdleme35.a
    atmod3i1
    syl131anc
    @13
    @19
    @15
    cK
    cp1
    cfv
    #
    c.an
    co
    #
    @15
    @13
    @18
    @29
    @15
    c.an
    @13
    @2
    @5
    @18
    @29
    wceq
    @2
    @5
    @6
    @11
    @12
    simp11
    @2
    @5
    @6
    @11
    @12
    simp12
    cA
    cP
    @29
    cH
    c.or
    cK
    c.le
    cW
    cdleme35.l
    cdleme35.j
    @29
    eqid
    #
    cdleme35.a
    cdleme35.h
    lhpjat2
    syl2anc
    oveq2d
    @13
    cK
    col
    wcel
    #
    @21
    @30
    @15
    wceq
    @13
    @0
    @32
    @24
    cK
    hlol
    syl
    @28
    @20
    @29
    cK
    c.an
    @15
    @27
    cdleme35.m
    @31
    olm11
    syl2anc
    eqtrd
    3eqtrd
end
