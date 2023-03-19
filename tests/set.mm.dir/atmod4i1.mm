include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "co.mm"
include "clat.mm"
include "wceq.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "simp22.mm"
include "simp23.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "simp21.mm"
include "atbase.mm"
include "syl.mm"
include "latjcom.mm"
include "atmod1i1.mm"
include "oveq1d.mm"
include "3eqtrd.mm"

theorem atmod4i1
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


  assert |- ( ( K e. HL /\ ( P e. A /\ X e. B /\ Y e. B ) /\ P .<_ Y ) -> ( ( X ./\ Y ) .\/ P ) = ( ( X .\/ P ) ./\ Y ) )

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
    cY
    c.le
    wbr
    #
    w3a
    #
    cX
    cY
    c.an
    co
    #
    cP
    c.or
    co
    #
    cP
    @7
    c.or
    co
    #
    cP
    cX
    c.or
    co
    #
    cY
    c.an
    co
    cX
    cP
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
    cP
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
    @6
    @12
    @2
    @3
    @13
    @15
    @0
    @1
    @2
    @3
    @5
    simp22
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
    cX
    cY
    atmod.b
    atmod.m
    latmcl
    syl3anc
    @6
    @1
    @14
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
    @7
    cP
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
    atmod1i1
    @6
    @10
    @11
    cY
    c.an
    @6
    @12
    @14
    @2
    @10
    @11
    wceq
    @15
    @17
    @16
    cB
    c.or
    cK
    cP
    cX
    atmod.b
    atmod.j
    latjcom
    syl3anc
    oveq1d
    3eqtrd
end
