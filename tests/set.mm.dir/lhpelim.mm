include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "cp0.mm"
include "cfv.mm"
include "wceq.mm"
include "eqid.mm"
include "lhpmat.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "simp1l.mm"
include "simp2l.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "simp3.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "latmle2.mm"
include "atmod4i2.mm"
include "syl131anc.mm"
include "col.mm"
include "hlol.mm"
include "olj02.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"

theorem lhpelim
  let cA: class A
  let cB: class B
  let cP: class P
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  assume lhpelim.b: |- B = ( Base ` K )
  assume lhpelim.l: |- .<_ = ( le ` K )
  assume lhpelim.j: |- .\/ = ( join ` K )
  assume lhpelim.m: |- ./\ = ( meet ` K )
  assume lhpelim.a: |- A = ( Atoms ` K )
  assume lhpelim.h: |- H = ( LHyp ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ X e. B ) -> ( ( P .\/ ( X ./\ W ) ) ./\ W ) = ( X ./\ W ) )

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
    cX
    cB
    wcel
    #
    w3a
    #
    cP
    cW
    c.an
    co
    #
    cX
    cW
    c.an
    co
    #
    c.or
    co
    #
    cK
    cp0
    cfv
    #
    @9
    c.or
    co
    #
    cP
    @9
    c.or
    co
    cW
    c.an
    co
    #
    @9
    @7
    @8
    @11
    @9
    c.or
    @2
    @5
    @8
    @11
    wceq
    @6
    cA
    cP
    cH
    cK
    c.le
    c.an
    cW
    @11
    lhpelim.l
    lhpelim.m
    @11
    eqid
    #
    lhpelim.a
    lhpelim.h
    lhpmat
    3adant3
    oveq1d
    @7
    @0
    @3
    @9
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    @9
    cW
    c.le
    wbr
    #
    @10
    @13
    wceq
    @0
    @1
    @5
    @6
    simp1l
    #
    @2
    @3
    @4
    @6
    simp2l
    @7
    cK
    clat
    wcel
    #
    @6
    @16
    @15
    @7
    @0
    @19
    @18
    cK
    hllat
    syl
    #
    @2
    @5
    @6
    simp3
    #
    @7
    @1
    @16
    @0
    @1
    @5
    @6
    simp1r
    cB
    cH
    cK
    cW
    lhpelim.b
    lhpelim.h
    lhpbase
    syl
    #
    cB
    cK
    c.an
    cX
    cW
    lhpelim.b
    lhpelim.m
    latmcl
    syl3anc
    #
    @22
    @7
    @19
    @6
    @16
    @17
    @20
    @21
    @22
    cB
    cK
    c.le
    c.an
    cX
    cW
    lhpelim.b
    lhpelim.l
    lhpelim.m
    latmle2
    syl3anc
    cA
    cB
    cP
    c.or
    cK
    c.le
    c.an
    @9
    cW
    lhpelim.b
    lhpelim.l
    lhpelim.j
    lhpelim.m
    lhpelim.a
    atmod4i2
    syl131anc
    @7
    cK
    col
    wcel
    #
    @15
    @12
    @9
    wceq
    @7
    @0
    @24
    @18
    cK
    hlol
    syl
    @23
    cB
    c.or
    cK
    @9
    @11
    lhpelim.b
    lhpelim.j
    @14
    olj02
    syl2anc
    3eqtr3d
end
