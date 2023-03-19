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
include "latmcom.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "simp21.mm"
include "atbase.mm"
include "syl.mm"
include "latmcl.mm"
include "latjcom.mm"
include "latjcl.mm"
include "simp1.mm"
include "simp3.mm"
include "atmod1i1.mm"
include "syl131anc.mm"
include "3eqtr4d.mm"
include "3eqtr3d.mm"

theorem atmod2i1
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


  assert |- ( ( K e. HL /\ ( P e. A /\ X e. B /\ Y e. B ) /\ P .<_ X ) -> ( ( X ./\ Y ) .\/ P ) = ( X ./\ ( Y .\/ P ) ) )

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
    cX
    cY
    c.an
    co
    #
    c.or
    co
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
    @7
    cP
    c.or
    co
    #
    cX
    cY
    cP
    c.or
    co
    #
    c.an
    co
    #
    @6
    @7
    @9
    cP
    c.or
    @6
    cK
    clat
    wcel
    #
    @2
    @3
    @7
    @9
    wceq
    @0
    @4
    @14
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
    simp22
    #
    @0
    @1
    @2
    @3
    @5
    simp23
    #
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
    @14
    cP
    cB
    wcel
    #
    @7
    cB
    wcel
    #
    @8
    @11
    wceq
    @15
    @6
    @1
    @18
    @0
    @1
    @2
    @3
    @5
    simp21
    #
    cA
    cB
    cP
    cK
    atmod.b
    atmod.a
    atbase
    syl
    #
    @6
    @14
    @2
    @3
    @19
    @15
    @16
    @17
    cB
    cK
    c.an
    cX
    cY
    atmod.b
    atmod.m
    latmcl
    syl3anc
    cB
    c.or
    cK
    cP
    @7
    atmod.b
    atmod.j
    latjcom
    syl3anc
    @6
    cP
    cY
    c.or
    co
    #
    cX
    c.an
    co
    #
    cX
    @22
    c.an
    co
    #
    @10
    @13
    @6
    @14
    @22
    cB
    wcel
    #
    @2
    @23
    @24
    wceq
    @15
    @6
    @14
    @18
    @3
    @25
    @15
    @21
    @17
    cB
    c.or
    cK
    cP
    cY
    atmod.b
    atmod.j
    latjcl
    syl3anc
    @16
    cB
    cK
    c.an
    @22
    cX
    atmod.b
    atmod.m
    latmcom
    syl3anc
    @6
    @0
    @1
    @3
    @2
    @5
    @10
    @23
    wceq
    @0
    @4
    @5
    simp1
    @20
    @17
    @16
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
    @12
    @22
    cX
    c.an
    @6
    @14
    @3
    @18
    @12
    @22
    wceq
    @15
    @17
    @21
    cB
    c.or
    cK
    cY
    cP
    atmod.b
    atmod.j
    latjcom
    syl3anc
    oveq2d
    3eqtr4d
    3eqtr3d
end
