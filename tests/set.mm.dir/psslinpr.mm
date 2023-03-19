include "cnp.mm"
include "wcel.mm"
include "wa.mm"
include "wpss.mm"
include "wceq.mm"
include "wo.mm"
include "w3o.mm"
include "cv.mm"
include "wn.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "cltq.mm"
include "wbr.mm"
include "cnq.mm"
include "elprnq.mm"
include "prub.mm"
include "sylan2.mm"
include "prcdnq.mm"
include "adantl.mm"
include "syld.mm"
include "exp43.mm"
include "com3r.mm"
include "imp.mm"
include "imp4a.mm"
include "com23.mm"
include "alrimdv.mm"
include "exlimdv.mm"
include "wss.mm"
include "nss.mm"
include "sspss.mm"
include "xchnxbi.mm"
include "dfss2.mm"
include "bitr3i.mm"
include "3imtr4g.mm"
include "orrd.mm"
include "df-3or.mm"
include "or32.mm"
include "orordir.mm"
include "eqcom.mm"
include "orbi2i.mm"
include "bitr4i.mm"
include "3bitri.mm"
include "sylibr.mm"

theorem psslinpr
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. P. /\ B e. P. ) -> ( A C. B \/ A = B \/ B C. A ) )

  proof
    cA
    cnp
    wcel
    #
    cB
    cnp
    wcel
    #
    wa
    #
    cA
    cB
    wpss
    #
    cA
    cB
    wceq
    #
    wo
    #
    cB
    cA
    wpss
    #
    cB
    cA
    wceq
    #
    wo
    #
    wo
    #
    @3
    @4
    @6
    w3o
    #
    @2
    @5
    @8
    @2
    vx
    cv
    #
    cA
    wcel
    #
    @11
    cB
    wcel
    wn
    #
    wa
    #
    vx
    wex
    #
    vy
    cv
    #
    cB
    wcel
    #
    @16
    cA
    wcel
    #
    wi
    #
    vy
    wal
    #
    @5
    wn
    @8
    @2
    @14
    @20
    vx
    @2
    @14
    @19
    vy
    @2
    @17
    @14
    @18
    @2
    @17
    @12
    @13
    @18
    @0
    @1
    @17
    @12
    @13
    @18
    wi
    #
    wi
    #
    wi
    @1
    @17
    @0
    @22
    @1
    @17
    @0
    @12
    @21
    @1
    @17
    wa
    #
    @0
    @12
    wa
    #
    wa
    @13
    @16
    @11
    cltq
    wbr
    #
    @18
    @24
    @23
    @11
    cnq
    wcel
    @13
    @25
    wi
    cA
    @11
    elprnq
    cB
    @16
    @11
    prub
    sylan2
    @24
    @25
    @18
    wi
    @23
    cA
    @11
    @16
    prcdnq
    adantl
    syld
    exp43
    com3r
    imp
    imp4a
    com23
    alrimdv
    exlimdv
    cA
    cB
    wss
    @15
    @5
    vx
    cA
    cB
    nss
    cA
    cB
    sspss
    xchnxbi
    @8
    cB
    cA
    wss
    @20
    cB
    cA
    sspss
    vy
    cB
    cA
    dfss2
    bitr3i
    3imtr4g
    orrd
    @10
    @5
    @6
    wo
    @3
    @6
    wo
    @4
    wo
    #
    @9
    @3
    @4
    @6
    df-3or
    @3
    @4
    @6
    or32
    @26
    @5
    @6
    @4
    wo
    #
    wo
    @9
    @3
    @6
    @4
    orordir
    @8
    @27
    @5
    @7
    @4
    @6
    cB
    cA
    eqcom
    orbi2i
    orbi2i
    bitr4i
    3bitri
    sylibr
end
