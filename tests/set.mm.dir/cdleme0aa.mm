include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "clat.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "atbase.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "syl5eqel.mm"

theorem cdleme0aa
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdleme0.l: |- .<_ = ( le ` K )
  assume cdleme0.j: |- .\/ = ( join ` K )
  assume cdleme0.m: |- ./\ = ( meet ` K )
  assume cdleme0.a: |- A = ( Atoms ` K )
  assume cdleme0.h: |- H = ( LHyp ` K )
  assume cdleme0.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme0.b: |- B = ( Base ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ P e. A /\ Q e. A ) -> U e. B )

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
    w3a
    #
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
    cB
    cdleme0.u
    @5
    cK
    clat
    wcel
    #
    @6
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    @7
    cB
    wcel
    @5
    @0
    @8
    @0
    @1
    @3
    @4
    simp1l
    cK
    hllat
    syl
    #
    @5
    @8
    cP
    cB
    wcel
    #
    cQ
    cB
    wcel
    #
    @9
    @11
    @3
    @2
    @12
    @4
    cA
    cB
    cP
    cK
    cdleme0.b
    cdleme0.a
    atbase
    3ad2ant2
    @4
    @2
    @13
    @3
    cA
    cB
    cQ
    cK
    cdleme0.b
    cdleme0.a
    atbase
    3ad2ant3
    cB
    c.or
    cK
    cP
    cQ
    cdleme0.b
    cdleme0.j
    latjcl
    syl3anc
    @5
    @1
    @10
    @0
    @1
    @3
    @4
    simp1r
    cB
    cH
    cK
    cW
    cdleme0.b
    cdleme0.h
    lhpbase
    syl
    cB
    cK
    c.an
    @6
    cW
    cdleme0.b
    cdleme0.m
    latmcl
    syl3anc
    syl5eqel
end
