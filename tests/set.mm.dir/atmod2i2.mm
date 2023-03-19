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
include "latjcom.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "simp22.mm"
include "latjcl.mm"
include "latmcom.mm"
include "simp1.mm"
include "simp3.mm"
include "atmod1i2.mm"
include "syl131anc.mm"
include "3eqtr4d.mm"
include "latmcl.mm"
include "3eqtrrd.mm"

theorem atmod2i2
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


  assert |- ( ( K e. HL /\ ( P e. A /\ X e. B /\ Y e. B ) /\ Y .<_ X ) -> ( ( X ./\ P ) .\/ Y ) = ( X ./\ ( P .\/ Y ) ) )

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
    cY
    cX
    c.le
    wbr
    #
    w3a
    #
    cX
    cP
    cY
    c.or
    co
    #
    c.an
    co
    #
    cY
    cP
    cX
    c.an
    co
    #
    c.or
    co
    #
    @9
    cY
    c.or
    co
    #
    cX
    cP
    c.an
    co
    #
    cY
    c.or
    co
    @6
    @7
    cX
    c.an
    co
    #
    cY
    cP
    c.or
    co
    #
    cX
    c.an
    co
    #
    @8
    @10
    @6
    @7
    @14
    cX
    c.an
    @6
    cK
    clat
    wcel
    #
    cP
    cB
    wcel
    #
    @3
    @7
    @14
    wceq
    @0
    @4
    @16
    @5
    cK
    hllat
    3ad2ant1
    #
    @6
    @1
    @17
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
    @0
    @1
    @2
    @3
    @5
    simp23
    #
    cB
    c.or
    cK
    cP
    cY
    atmod.b
    atmod.j
    latjcom
    syl3anc
    oveq1d
    @6
    @16
    @2
    @7
    cB
    wcel
    #
    @8
    @13
    wceq
    @18
    @0
    @1
    @2
    @3
    @5
    simp22
    #
    @6
    @16
    @17
    @3
    @22
    @18
    @20
    @21
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
    @7
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
    @15
    wceq
    @0
    @4
    @5
    simp1
    @19
    @21
    @23
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
    atmod1i2
    syl131anc
    3eqtr4d
    @6
    @16
    @3
    @9
    cB
    wcel
    #
    @10
    @11
    wceq
    @18
    @21
    @6
    @16
    @17
    @2
    @24
    @18
    @20
    @23
    cB
    cK
    c.an
    cP
    cX
    atmod.b
    atmod.m
    latmcl
    syl3anc
    cB
    c.or
    cK
    cY
    @9
    atmod.b
    atmod.j
    latjcom
    syl3anc
    @6
    @9
    @12
    cY
    c.or
    @6
    @16
    @17
    @2
    @9
    @12
    wceq
    @18
    @20
    @23
    cB
    cK
    c.an
    cP
    cX
    atmod.b
    atmod.m
    latmcom
    syl3anc
    oveq1d
    3eqtrrd
end
