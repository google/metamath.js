include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "cp1.mm"
include "cfv.mm"
include "wceq.mm"
include "eqid.mm"
include "lhpjat2.mm"
include "3adant3.mm"
include "oveq2d.mm"
include "oveq2i.mm"
include "simp1l.mm"
include "simp2l.mm"
include "simp3l.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "syl.mm"
include "hlatlej1.mm"
include "atmod3i1.mm"
include "syl131anc.mm"
include "syl5req.mm"
include "col.mm"
include "hlol.mm"
include "olm11.mm"
include "syl2anc.mm"
include "3eqtr3rd.mm"

theorem cdleme42a
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  assume cdleme42.b: |- B = ( Base ` K )
  assume cdleme42.l: |- .<_ = ( le ` K )
  assume cdleme42.j: |- .\/ = ( join ` K )
  assume cdleme42.m: |- ./\ = ( meet ` K )
  assume cdleme42.a: |- A = ( Atoms ` K )
  assume cdleme42.h: |- H = ( LHyp ` K )
  assume cdleme42.v: |- V = ( ( R .\/ S ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) -> ( R .\/ S ) = ( R .\/ V ) )

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
    cS
    cA
    wcel
    #
    cS
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
    cS
    c.or
    co
    #
    cR
    cW
    c.or
    co
    #
    c.an
    co
    #
    @10
    cK
    cp1
    cfv
    #
    c.an
    co
    #
    cR
    cV
    c.or
    co
    #
    @10
    @9
    @11
    @13
    @10
    c.an
    @2
    @5
    @11
    @13
    wceq
    @8
    cA
    cR
    @13
    cH
    c.or
    cK
    c.le
    cW
    cdleme42.l
    cdleme42.j
    @13
    eqid
    #
    cdleme42.a
    cdleme42.h
    lhpjat2
    3adant3
    oveq2d
    @9
    @15
    cR
    @10
    cW
    c.an
    co
    #
    c.or
    co
    #
    @12
    cV
    @17
    cR
    c.or
    cdleme42.v
    oveq2i
    @9
    @0
    @3
    @10
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    cR
    @10
    c.le
    wbr
    #
    @18
    @12
    wceq
    @0
    @1
    @5
    @8
    simp1l
    #
    @2
    @3
    @4
    @8
    simp2l
    #
    @9
    @0
    @3
    @6
    @19
    @22
    @23
    @2
    @5
    @6
    @7
    simp3l
    #
    cA
    cB
    c.or
    cK
    cR
    cS
    cdleme42.b
    cdleme42.j
    cdleme42.a
    hlatjcl
    syl3anc
    #
    @9
    @1
    @20
    @0
    @1
    @5
    @8
    simp1r
    cB
    cH
    cK
    cW
    cdleme42.b
    cdleme42.h
    lhpbase
    syl
    @9
    @0
    @3
    @6
    @21
    @22
    @23
    @24
    cA
    cR
    cS
    c.or
    cK
    c.le
    cdleme42.l
    cdleme42.j
    cdleme42.a
    hlatlej1
    syl3anc
    cA
    cB
    cR
    c.or
    cK
    c.le
    c.an
    @10
    cW
    cdleme42.b
    cdleme42.l
    cdleme42.j
    cdleme42.m
    cdleme42.a
    atmod3i1
    syl131anc
    syl5req
    @9
    cK
    col
    wcel
    #
    @19
    @14
    @10
    wceq
    @9
    @0
    @26
    @22
    cK
    hlol
    syl
    @25
    cB
    @13
    cK
    c.an
    @10
    cdleme42.b
    cdleme42.m
    @16
    olm11
    syl2anc
    3eqtr3rd
end
