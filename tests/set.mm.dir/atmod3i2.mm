include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "co.mm"
include "clat.mm"
include "wceq.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "simp23.mm"
include "simp22.mm"
include "simp21.mm"
include "atbase.mm"
include "syl.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "latmcom.mm"
include "atmod1i2.mm"
include "oveq2d.mm"
include "3eqtr2rd.mm"

theorem atmod3i2
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


  assert |- ( ( K e. HL /\ ( P e. A /\ X e. B /\ Y e. B ) /\ X .<_ Y ) -> ( X .\/ ( Y ./\ P ) ) = ( Y ./\ ( X .\/ P ) ) )

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
    cX
    cY
    c.le
    wbr
    #
    w3a
    #
    cY
    cX
    cP
    c.or
    co
    #
    c.an
    co
    #
    @7
    cY
    c.an
    co
    #
    cX
    cP
    cY
    c.an
    co
    #
    c.or
    co
    cX
    cY
    cP
    c.an
    co
    #
    c.or
    co
    @6
    cK
    clat
    wcel
    #
    @3
    @7
    cB
    wcel
    #
    @8
    @9
    wceq
    @0
    @4
    @12
    @5
    cK
    hllat
    3ad2ant1
    #
    @0
    @1
    @2
    @3
    @5
    simp23
    #
    @6
    @12
    @2
    cP
    cB
    wcel
    #
    @13
    @14
    @0
    @1
    @2
    @3
    @5
    simp22
    @6
    @1
    @16
    @0
    @1
    @2
    @3
    @5
    simp21
    cA
    cB
    cP
    cK
    atmod.b
    atmod.a
    atbase
    syl
    #
    cB
    c.or
    cK
    cX
    cP
    atmod.b
    atmod.j
    latjcl
    syl3anc
    cB
    cK
    c.an
    cY
    @7
    atmod.b
    atmod.m
    latmcom
    syl3anc
    cA
    cB
    cP
    c.or
    cK
    c.le
    c.an
    cX
    cY
    atmod.b
    atmod.l
    atmod.j
    atmod.m
    atmod.a
    atmod1i2
    @6
    @10
    @11
    cX
    c.or
    @6
    @12
    @16
    @3
    @10
    @11
    wceq
    @14
    @17
    @15
    cB
    cK
    c.an
    cP
    cY
    atmod.b
    atmod.m
    latmcom
    syl3anc
    oveq2d
    3eqtr2rd
end
