include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "clat.mm"
include "hllat.mm"
include "ad2antrr.mm"
include "simpll.mm"
include "simprl.mm"
include "simprr.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "lhpbase.mm"
include "ad2antlr.mm"
include "latmcl.mm"
include "syl5eqel.mm"

theorem cdlemedb
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdlemeda.l: |- .<_ = ( le ` K )
  assume cdlemeda.j: |- .\/ = ( join ` K )
  assume cdlemeda.m: |- ./\ = ( meet ` K )
  assume cdlemeda.a: |- A = ( Atoms ` K )
  assume cdlemeda.h: |- H = ( LHyp ` K )
  assume cdlemeda.d: |- D = ( ( R .\/ S ) ./\ W )
  assume cdlemedb.b: |- B = ( Base ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( R e. A /\ S e. A ) ) -> D e. B )

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
    cS
    cA
    wcel
    #
    wa
    #
    wa
    #
    cD
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
    cdlemeda.d
    @6
    cK
    clat
    wcel
    #
    @7
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    @8
    cB
    wcel
    @0
    @9
    @1
    @5
    cK
    hllat
    ad2antrr
    @6
    @0
    @3
    @4
    @10
    @0
    @1
    @5
    simpll
    @2
    @3
    @4
    simprl
    @2
    @3
    @4
    simprr
    cA
    cB
    c.or
    cK
    cR
    cS
    cdlemedb.b
    cdlemeda.j
    cdlemeda.a
    hlatjcl
    syl3anc
    @1
    @11
    @0
    @5
    cB
    cH
    cK
    cW
    cdlemedb.b
    cdlemeda.h
    lhpbase
    ad2antlr
    cB
    cK
    c.an
    @7
    cW
    cdlemedb.b
    cdlemeda.m
    latmcl
    syl3anc
    syl5eqel
end
