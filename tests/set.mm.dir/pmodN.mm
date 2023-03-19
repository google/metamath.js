include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "cin.mm"
include "co.mm"
include "incom.mm"
include "clat.mm"
include "wceq.mm"
include "hllat.mm"
include "adantr.mm"
include "simpr2.mm"
include "inss2.mm"
include "simpr3.mm"
include "syl5ss.mm"
include "paddcom.mm"
include "syl3anc.mm"
include "ineq2d.mm"
include "oveq2i.mm"
include "simpr1.mm"
include "3jca.mm"
include "inss1.mm"
include "pmod1i.mm"
include "mpi.mm"
include "syldan.mm"
include "3eqtr4a.mm"

theorem pmodN
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


  assert |- ( ( K e. HL /\ ( X e. S /\ Y C_ A /\ Z C_ A ) ) -> ( X i^i ( Y .+ ( X i^i Z ) ) ) = ( ( X i^i Y ) .+ ( X i^i Z ) ) )

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
    wa
    #
    cX
    cX
    cZ
    cin
    #
    cY
    c.pl
    co
    #
    cin
    @7
    cX
    cin
    #
    cX
    cY
    @6
    c.pl
    co
    #
    cin
    cX
    cY
    cin
    #
    @6
    c.pl
    co
    #
    cX
    @7
    incom
    @5
    @9
    @7
    cX
    @5
    cK
    clat
    wcel
    #
    @2
    @6
    cA
    wss
    #
    @9
    @7
    wceq
    @0
    @12
    @4
    cK
    hllat
    adantr
    #
    @0
    @1
    @2
    @3
    simpr2
    #
    @5
    @6
    cZ
    cA
    cX
    cZ
    inss2
    @0
    @1
    @2
    @3
    simpr3
    syl5ss
    #
    cA
    c.pl
    cK
    cY
    @6
    pmod.a
    pmod.p
    paddcom
    syl3anc
    ineq2d
    @5
    @6
    @10
    c.pl
    co
    #
    @6
    cY
    cX
    cin
    #
    c.pl
    co
    #
    @11
    @8
    @10
    @18
    @6
    c.pl
    cX
    cY
    incom
    oveq2i
    @5
    @12
    @10
    cA
    wss
    @13
    @11
    @17
    wceq
    @14
    @5
    @10
    cY
    cA
    cX
    cY
    inss2
    @15
    syl5ss
    @16
    cA
    c.pl
    cK
    @10
    @6
    pmod.a
    pmod.p
    paddcom
    syl3anc
    @0
    @4
    @13
    @2
    @1
    w3a
    #
    @8
    @19
    wceq
    #
    @5
    @13
    @2
    @1
    @16
    @15
    @0
    @1
    @2
    @3
    simpr1
    3jca
    @0
    @20
    wa
    @6
    cX
    wss
    @21
    cX
    cZ
    inss1
    cA
    c.pl
    cS
    cK
    @6
    cY
    cX
    pmod.a
    pmod.s
    pmod.p
    pmod1i
    mpi
    syldan
    3eqtr4a
    3eqtr4a
end
