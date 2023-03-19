include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "clat.mm"
include "hllat.mm"
include "ad2antrr.mm"
include "simpr3.mm"
include "atbase.mm"
include "syl.mm"
include "cdleme0aa.mm"
include "3adant3r3.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simpr2.mm"
include "simpr1.mm"
include "lhpbase.mm"
include "ad2antlr.mm"
include "latmcl.mm"
include "syl5eqel.mm"

theorem cdleme1b
  let cA: class A
  let cB: class B
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
  assume cdleme1.b: |- B = ( Base ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ Q e. A /\ R e. A ) ) -> F e. B )

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
    w3a
    #
    wa
    #
    cF
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
    cB
    cdleme1.f
    @7
    cK
    clat
    wcel
    #
    @8
    cB
    wcel
    #
    @11
    cB
    wcel
    #
    @12
    cB
    wcel
    @0
    @13
    @1
    @6
    cK
    hllat
    ad2antrr
    #
    @7
    @13
    cR
    cB
    wcel
    #
    cU
    cB
    wcel
    #
    @14
    @16
    @7
    @5
    @17
    @2
    @3
    @4
    @5
    simpr3
    cA
    cB
    cR
    cK
    cdleme1.b
    cdleme1.a
    atbase
    syl
    #
    @2
    @3
    @4
    @18
    @5
    cA
    cB
    cP
    cQ
    cU
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
    cdleme1.b
    cdleme0aa
    3adant3r3
    cB
    c.or
    cK
    cR
    cU
    cdleme1.b
    cdleme1.j
    latjcl
    syl3anc
    @7
    @13
    cQ
    cB
    wcel
    #
    @10
    cB
    wcel
    #
    @15
    @16
    @7
    @4
    @20
    @2
    @3
    @4
    @5
    simpr2
    cA
    cB
    cQ
    cK
    cdleme1.b
    cdleme1.a
    atbase
    syl
    @7
    @13
    @9
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    @21
    @16
    @7
    @13
    cP
    cB
    wcel
    #
    @17
    @22
    @16
    @7
    @3
    @24
    @2
    @3
    @4
    @5
    simpr1
    cA
    cB
    cP
    cK
    cdleme1.b
    cdleme1.a
    atbase
    syl
    @19
    cB
    c.or
    cK
    cP
    cR
    cdleme1.b
    cdleme1.j
    latjcl
    syl3anc
    @1
    @23
    @0
    @6
    cB
    cH
    cK
    cW
    cdleme1.b
    cdleme1.h
    lhpbase
    ad2antlr
    cB
    cK
    c.an
    @9
    cW
    cdleme1.b
    cdleme1.m
    latmcl
    syl3anc
    cB
    c.or
    cK
    cQ
    @10
    cdleme1.b
    cdleme1.j
    latjcl
    syl3anc
    cB
    cK
    c.an
    @8
    @11
    cdleme1.b
    cdleme1.m
    latmcl
    syl3anc
    syl5eqel
end
