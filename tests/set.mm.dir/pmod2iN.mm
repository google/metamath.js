include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cin.mm"
include "co.mm"
include "wceq.mm"
include "incom.mm"
include "oveq1i.mm"
include "clat.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "simp22.mm"
include "ssinss1.mm"
include "syl.mm"
include "simp23.mm"
include "paddcom.mm"
include "syl3anc.mm"
include "syl5eq.mm"
include "simp21.mm"
include "3jca.mm"
include "pmod1i.mm"
include "3impia.mm"
include "syld3an2.mm"
include "ineq1d.mm"
include "3eqtr2d.mm"
include "syl6eq.mm"
include "3expia.mm"

theorem pmod2iN
  let cA: class A
  let c.pl: class .+
  let cS: class S
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume pmod.a: |- A = ( Atoms ` K )
  assume pmod.s: |- S = ( PSubSp ` K )
  assume pmod.p: |- .+ = ( +P ` K )


  assert |- ( ( K e. HL /\ ( X e. S /\ Y C_ A /\ Z C_ A ) ) -> ( Z C_ X -> ( ( X i^i Y ) .+ Z ) = ( X i^i ( Y .+ Z ) ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cS
    wcel
    #
    cY
    cA
    wss
    #
    cZ
    cA
    wss
    #
    w3a
    #
    cZ
    cX
    wss
    #
    cX
    cY
    cin
    #
    cZ
    c.pl
    co
    #
    cX
    cY
    cZ
    c.pl
    co
    #
    cin
    #
    wceq
    @0
    @4
    @5
    w3a
    #
    @7
    @8
    cX
    cin
    #
    @9
    @10
    @7
    cZ
    cY
    cX
    cin
    #
    c.pl
    co
    #
    cZ
    cY
    c.pl
    co
    #
    cX
    cin
    #
    @11
    @10
    @7
    @12
    cZ
    c.pl
    co
    #
    @13
    @6
    @12
    cZ
    c.pl
    cX
    cY
    incom
    oveq1i
    @10
    cK
    clat
    wcel
    #
    @12
    cA
    wss
    #
    @3
    @16
    @13
    wceq
    @0
    @4
    @17
    @5
    cK
    hllat
    3ad2ant1
    #
    @10
    @2
    @18
    @0
    @1
    @2
    @3
    @5
    simp22
    #
    cY
    cX
    cA
    ssinss1
    syl
    @0
    @1
    @2
    @3
    @5
    simp23
    #
    cA
    c.pl
    cK
    @12
    cZ
    pmod.a
    pmod.p
    paddcom
    syl3anc
    syl5eq
    @0
    @3
    @2
    @1
    w3a
    #
    @4
    @5
    @15
    @13
    wceq
    #
    @10
    @3
    @2
    @1
    @21
    @20
    @0
    @1
    @2
    @3
    @5
    simp21
    3jca
    @0
    @22
    @5
    @23
    cA
    c.pl
    cS
    cK
    cZ
    cY
    cX
    pmod.a
    pmod.s
    pmod.p
    pmod1i
    3impia
    syld3an2
    @10
    @14
    @8
    cX
    @10
    @17
    @3
    @2
    @14
    @8
    wceq
    @19
    @21
    @20
    cA
    c.pl
    cK
    cZ
    cY
    pmod.a
    pmod.p
    paddcom
    syl3anc
    ineq1d
    3eqtr2d
    @8
    cX
    incom
    syl6eq
    3expia
end
