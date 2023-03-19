include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "clat.mm"
include "hllat.mm"
include "adantr.mm"
include "hlatjcl.mm"
include "3adant3r3.mm"
include "simpr3.mm"
include "lhpbase.mm"
include "syl.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "syl5eqel.mm"

theorem cdleme9b
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let cW: class W
  assume cdleme9b.b: |- B = ( Base ` K )
  assume cdleme9b.j: |- .\/ = ( join ` K )
  assume cdleme9b.m: |- ./\ = ( meet ` K )
  assume cdleme9b.a: |- A = ( Atoms ` K )
  assume cdleme9b.h: |- H = ( LHyp ` K )
  assume cdleme9b.c: |- C = ( ( P .\/ S ) ./\ W )


  assert |- ( ( K e. HL /\ ( P e. A /\ S e. A /\ W e. H ) ) -> C e. B )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    cW
    cH
    wcel
    #
    w3a
    #
    wa
    #
    cC
    cP
    cS
    c.or
    co
    #
    cW
    c.an
    co
    #
    cB
    cdleme9b.c
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
    @0
    @8
    @4
    cK
    hllat
    adantr
    @0
    @1
    @2
    @9
    @3
    cA
    cB
    c.or
    cK
    cP
    cS
    cdleme9b.b
    cdleme9b.j
    cdleme9b.a
    hlatjcl
    3adant3r3
    @5
    @3
    @10
    @0
    @1
    @2
    @3
    simpr3
    cB
    cH
    cK
    cW
    cdleme9b.b
    cdleme9b.h
    lhpbase
    syl
    cB
    cK
    c.an
    @6
    cW
    cdleme9b.b
    cdleme9b.m
    latmcl
    syl3anc
    syl5eqel
end
