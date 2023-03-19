include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "oveq2i.mm"
include "cp1.mm"
include "cfv.mm"
include "cbs.mm"
include "wceq.mm"
include "simp1l.mm"
include "simp23l.mm"
include "simp21.mm"
include "simp22.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "syl.mm"
include "simp3.mm"
include "atmod3i1.mm"
include "syl131anc.mm"
include "simp1.mm"
include "simp23.mm"
include "lhpjat2.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "col.mm"
include "hlol.mm"
include "olm11.mm"
include "3eqtrd.mm"
include "syl5req.mm"

theorem cdleme4
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdleme4.l: |- .<_ = ( le ` K )
  assume cdleme4.j: |- .\/ = ( join ` K )
  assume cdleme4.m: |- ./\ = ( meet ` K )
  assume cdleme4.a: |- A = ( Atoms ` K )
  assume cdleme4.h: |- H = ( LHyp ` K )
  assume cdleme4.u: |- U = ( ( P .\/ Q ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ Q e. A /\ ( R e. A /\ -. R .<_ W ) ) /\ R .<_ ( P .\/ Q ) ) -> ( P .\/ Q ) = ( R .\/ U ) )

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
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    w3a
    #
    cR
    cU
    c.or
    co
    cR
    @9
    cW
    c.an
    co
    #
    c.or
    co
    #
    @9
    cU
    @12
    cR
    c.or
    cdleme4.u
    oveq2i
    @11
    @13
    @9
    cR
    cW
    c.or
    co
    #
    c.an
    co
    #
    @9
    cK
    cp1
    cfv
    #
    c.an
    co
    #
    @9
    @11
    @0
    @5
    @9
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @18
    wcel
    #
    @10
    @13
    @15
    wceq
    @0
    @1
    @8
    @10
    simp1l
    #
    @5
    @6
    @3
    @4
    @2
    @10
    simp23l
    @11
    @0
    @3
    @4
    @19
    @21
    @2
    @3
    @4
    @7
    @10
    simp21
    @2
    @3
    @4
    @7
    @10
    simp22
    cA
    @18
    c.or
    cK
    cP
    cQ
    @18
    eqid
    #
    cdleme4.j
    cdleme4.a
    hlatjcl
    syl3anc
    #
    @11
    @1
    @20
    @0
    @1
    @8
    @10
    simp1r
    @18
    cH
    cK
    cW
    @22
    cdleme4.h
    lhpbase
    syl
    @2
    @8
    @10
    simp3
    cA
    @18
    cR
    c.or
    cK
    c.le
    c.an
    @9
    cW
    @22
    cdleme4.l
    cdleme4.j
    cdleme4.m
    cdleme4.a
    atmod3i1
    syl131anc
    @11
    @14
    @16
    @9
    c.an
    @11
    @2
    @7
    @14
    @16
    wceq
    @2
    @8
    @10
    simp1
    @2
    @3
    @4
    @7
    @10
    simp23
    cA
    cR
    @16
    cH
    c.or
    cK
    c.le
    cW
    cdleme4.l
    cdleme4.j
    @16
    eqid
    #
    cdleme4.a
    cdleme4.h
    lhpjat2
    syl2anc
    oveq2d
    @11
    cK
    col
    wcel
    #
    @19
    @17
    @9
    wceq
    @11
    @0
    @25
    @21
    cK
    hlol
    syl
    @23
    @18
    @16
    cK
    c.an
    @9
    @22
    cdleme4.m
    @24
    olm11
    syl2anc
    3eqtrd
    syl5req
end
