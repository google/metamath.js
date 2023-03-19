include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "co.mm"
include "clat.mm"
include "wceq.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "simp21.mm"
include "atbase.mm"
include "syl.mm"
include "simp23.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "simp22.mm"
include "latjcom.mm"
include "atmod1i2.mm"
include "oveq1d.mm"
include "3eqtrd.mm"

theorem atmod4i2
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


  assert |- ( ( K e. HL /\ ( P e. A /\ X e. B /\ Y e. B ) /\ X .<_ Y ) -> ( ( P ./\ Y ) .\/ X ) = ( ( P .\/ X ) ./\ Y ) )

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
    cP
    cY
    c.an
    co
    #
    cX
    c.or
    co
    #
    cX
    @7
    c.or
    co
    #
    cX
    cP
    c.or
    co
    #
    cY
    c.an
    co
    cP
    cX
    c.or
    co
    #
    cY
    c.an
    co
    @6
    cK
    clat
    wcel
    #
    @7
    cB
    wcel
    #
    @2
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
    @6
    @12
    cP
    cB
    wcel
    #
    @3
    @13
    @14
    @6
    @1
    @15
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
    @0
    @1
    @2
    @3
    @5
    simp23
    cB
    cK
    c.an
    cP
    cY
    atmod.b
    atmod.m
    latmcl
    syl3anc
    @0
    @1
    @2
    @3
    @5
    simp22
    #
    cB
    c.or
    cK
    @7
    cX
    atmod.b
    atmod.j
    latjcom
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
    cY
    c.an
    @6
    @12
    @2
    @15
    @10
    @11
    wceq
    @14
    @17
    @16
    cB
    c.or
    cK
    cX
    cP
    atmod.b
    atmod.j
    latjcom
    syl3anc
    oveq1d
    3eqtrd
end
