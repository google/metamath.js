include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "csn.mm"
include "co.mm"
include "club.mm"
include "cfv.mm"
include "cjn.mm"
include "cpmap.mm"
include "cbs.mm"
include "wceq.mm"
include "ccla.mm"
include "wss.mm"
include "hlclat.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "psubclssatN.mm"
include "eqid.mm"
include "atssbase.mm"
include "syl6ss.mm"
include "3adant3.mm"
include "clatlubcl.mm"
include "syl2anc.mm"
include "pmapjat1.mm"
include "syld3an2.mm"
include "pmapidclN.mm"
include "pmapat.mm"
include "3adant2.mm"
include "oveq12d.mm"
include "eqtr2d.mm"
include "simp1.mm"
include "clat.mm"
include "hllat.mm"
include "atbase.mm"
include "3ad2ant3.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "pmapsubclN.mm"
include "eqeltrd.mm"

theorem paddatclN
  let cA: class A
  let cC: class C
  let c.pl: class .+
  let cQ: class Q
  let cK: class K
  let cX: class X
  assume paddatcl.a: |- A = ( Atoms ` K )
  assume paddatcl.p: |- .+ = ( +P ` K )
  assume paddatcl.c: |- C = ( PSubCl ` K )


  assert |- ( ( K e. HL /\ X e. C /\ Q e. A ) -> ( X .+ { Q } ) e. C )

  proof
    cK
    chlt
    wcel
    #
    cX
    cC
    wcel
    #
    cQ
    cA
    wcel
    #
    w3a
    #
    cX
    cQ
    csn
    #
    c.pl
    co
    #
    cX
    cK
    club
    cfv
    #
    cfv
    #
    cQ
    cK
    cjn
    cfv
    #
    co
    #
    cK
    cpmap
    cfv
    #
    cfv
    #
    cC
    @3
    @11
    @7
    @10
    cfv
    #
    cQ
    @10
    cfv
    #
    c.pl
    co
    #
    @5
    @0
    @7
    cK
    cbs
    cfv
    #
    wcel
    #
    @1
    @2
    @11
    @14
    wceq
    @3
    cK
    ccla
    wcel
    #
    cX
    @15
    wss
    #
    @16
    @0
    @1
    @17
    @2
    cK
    hlclat
    3ad2ant1
    @0
    @1
    @18
    @2
    @0
    @1
    wa
    cX
    cA
    @15
    cA
    cC
    chlt
    cK
    cX
    paddatcl.a
    paddatcl.c
    psubclssatN
    cA
    @15
    cK
    @15
    eqid
    #
    paddatcl.a
    atssbase
    syl6ss
    3adant3
    @15
    cX
    @6
    cK
    @19
    @6
    eqid
    #
    clatlubcl
    syl2anc
    #
    cA
    @15
    c.pl
    cQ
    @8
    cK
    @10
    @7
    @19
    @8
    eqid
    #
    paddatcl.a
    @10
    eqid
    #
    paddatcl.p
    pmapjat1
    syld3an2
    @3
    @12
    cX
    @13
    @4
    c.pl
    @0
    @1
    @12
    cX
    wceq
    @2
    cC
    @6
    cK
    @10
    cX
    @20
    @23
    paddatcl.c
    pmapidclN
    3adant3
    @0
    @2
    @13
    @4
    wceq
    @1
    cA
    cQ
    cK
    @10
    paddatcl.a
    @23
    pmapat
    3adant2
    oveq12d
    eqtr2d
    @3
    @0
    @9
    @15
    wcel
    #
    @11
    cC
    wcel
    @0
    @1
    @2
    simp1
    @3
    cK
    clat
    wcel
    #
    @16
    cQ
    @15
    wcel
    #
    @24
    @0
    @1
    @25
    @2
    cK
    hllat
    3ad2ant1
    @21
    @2
    @0
    @26
    @1
    cA
    @15
    cQ
    cK
    @19
    paddatcl.a
    atbase
    3ad2ant3
    @15
    @8
    cK
    @7
    cQ
    @19
    @22
    latjcl
    syl3anc
    @15
    cC
    cK
    @10
    @9
    @19
    @23
    paddatcl.c
    pmapsubclN
    syl2anc
    eqeltrd
end
