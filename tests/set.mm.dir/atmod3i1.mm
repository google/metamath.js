include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "co.mm"
include "wceq.mm"
include "simp1.mm"
include "simp21.mm"
include "simp23.mm"
include "simp22.mm"
include "simp3.mm"
include "atmod1i1.mm"
include "syl131anc.mm"
include "clat.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "latmcom.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "atbase.mm"
include "syl.mm"
include "latjcl.mm"
include "3eqtr4d.mm"

theorem atmod3i1
  let cA: class A
  let cB: class B
  let cP: class P
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  assume atmod.b: |- B = ( Base ` K )
  assume atmod.l: |- .<_ = ( le ` K )
  assume atmod.j: |- .\/ = ( join ` K )
  assume atmod.m: |- ./\ = ( meet ` K )
  assume atmod.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ X e. B /\ Y e. B ) /\ P .<_ X ) -> ( P .\/ ( X ./\ Y ) ) = ( X ./\ ( P .\/ Y ) ) )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cP
    cX
    c.le
    wbr
    #
    w3a
    #
    cP
    cY
    cX
    c.an
    co
    #
    c.or
    co
    #
    cP
    cY
    c.or
    co
    #
    cX
    c.an
    co
    #
    cP
    cX
    cY
    c.an
    co
    #
    c.or
    co
    cX
    @9
    c.an
    co
    #
    @6
    @0
    @1
    @3
    @2
    @5
    @8
    @10
    wceq
    @0
    @4
    @5
    simp1
    @0
    @1
    @2
    @3
    @5
    simp21
    #
    @0
    @1
    @2
    @3
    @5
    simp23
    #
    @0
    @1
    @2
    @3
    @5
    simp22
    #
    @0
    @4
    @5
    simp3
    cA
    cB
    cP
    c.or
    cK
    c.le
    c.an
    cY
    cX
    atmod.b
    atmod.l
    atmod.j
    atmod.m
    atmod.a
    atmod1i1
    syl131anc
    @6
    @11
    @7
    cP
    c.or
    @6
    cK
    clat
    wcel
    #
    @2
    @3
    @11
    @7
    wceq
    @0
    @4
    @16
    @5
    cK
    hllat
    3ad2ant1
    #
    @15
    @14
    cB
    cK
    c.an
    cX
    cY
    atmod.b
    atmod.m
    latmcom
    syl3anc
    oveq2d
    @6
    @16
    @2
    @9
    cB
    wcel
    #
    @12
    @10
    wceq
    @17
    @15
    @6
    @16
    cP
    cB
    wcel
    #
    @3
    @18
    @17
    @6
    @1
    @19
    @13
    cA
    cB
    cP
    cK
    atmod.b
    atmod.a
    atbase
    syl
    @14
    cB
    c.or
    cK
    cP
    cY
    atmod.b
    atmod.j
    latjcl
    syl3anc
    cB
    cK
    c.an
    cX
    @9
    atmod.b
    atmod.m
    latmcom
    syl3anc
    3eqtr4d
end
