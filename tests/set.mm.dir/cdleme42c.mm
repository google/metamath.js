include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "simp2r.mm"
include "clat.mm"
include "wb.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp2l.mm"
include "atbase.mm"
include "simp3l.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "syl5eqel.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "simpl.mm"
include "syl6bir.mm"
include "mtod.mm"

theorem cdleme42c
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) -> -. ( R .\/ V ) .<_ W )

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
    #
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
    cV
    c.or
    co
    cW
    c.le
    wbr
    #
    @4
    @2
    @3
    @5
    @9
    simp2r
    @10
    @11
    @4
    cV
    cW
    c.le
    wbr
    #
    wa
    #
    @4
    @10
    cK
    clat
    wcel
    #
    cR
    cB
    wcel
    #
    cV
    cB
    wcel
    cW
    cB
    wcel
    #
    @13
    @11
    wb
    @10
    @0
    @14
    @0
    @1
    @6
    @9
    simp1l
    #
    cK
    hllat
    syl
    #
    @10
    @3
    @15
    @2
    @3
    @5
    @9
    simp2l
    #
    cA
    cB
    cR
    cK
    cdleme42.b
    cdleme42.a
    atbase
    syl
    @10
    cV
    cR
    cS
    c.or
    co
    #
    cW
    c.an
    co
    #
    cB
    cdleme42.v
    @10
    @14
    @20
    cB
    wcel
    #
    @16
    @21
    cB
    wcel
    @18
    @10
    @0
    @3
    @7
    @22
    @17
    @19
    @2
    @6
    @7
    @8
    simp3l
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
    @10
    @1
    @16
    @0
    @1
    @6
    @9
    simp1r
    cB
    cH
    cK
    cW
    cdleme42.b
    cdleme42.h
    lhpbase
    syl
    #
    cB
    cK
    c.an
    @20
    cW
    cdleme42.b
    cdleme42.m
    latmcl
    syl3anc
    syl5eqel
    @23
    cB
    c.or
    cK
    c.le
    cR
    cV
    cW
    cdleme42.b
    cdleme42.l
    cdleme42.j
    latjle12
    syl13anc
    @4
    @12
    simpl
    syl6bir
    mtod
end
