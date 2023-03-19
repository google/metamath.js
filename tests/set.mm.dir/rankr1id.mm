include "cr1.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "crnk.mm"
include "wceq.mm"
include "wss.mm"
include "ssid.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wb.mm"
include "csuc.mm"
include "cpw.mm"
include "fvex.mm"
include "pwid.mm"
include "r1sucg.mm"
include "syl5eleqr.mm"
include "r1elwf.mm"
include "syl.mm"
include "rankr1bg.mm"
include "mpancom.mm"
include "mpbii.mm"
include "rankonid.mm"
include "biimpi.mm"
include "onssr1.mm"
include "rankssb.mm"
include "sylc.mm"
include "eqsstr3d.mm"
include "eqssd.mm"
include "id.mm"
include "rankdmr1.mm"
include "syl6eqelr.mm"
include "impbii.mm"

theorem rankr1id
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. dom R1 <-> ( rank ` ( R1 ` A ) ) = A )

  proof
    cA
    cr1
    cdm
    #
    wcel
    #
    cA
    cr1
    cfv
    #
    crnk
    cfv
    #
    cA
    wceq
    #
    @1
    @3
    cA
    @1
    @2
    @2
    wss
    #
    @3
    cA
    wss
    #
    @2
    ssid
    @2
    cr1
    con0
    cima
    cuni
    wcel
    #
    @1
    @5
    @6
    wb
    @1
    @2
    cA
    csuc
    #
    cr1
    cfv
    #
    wcel
    @7
    @1
    @2
    @2
    cpw
    @9
    @2
    cA
    cr1
    fvex
    pwid
    cA
    r1sucg
    syl5eleqr
    @2
    @8
    r1elwf
    syl
    #
    @2
    cA
    rankr1bg
    mpancom
    mpbii
    @1
    cA
    cA
    crnk
    cfv
    #
    @3
    @1
    @11
    cA
    wceq
    cA
    rankonid
    biimpi
    @1
    @7
    cA
    @2
    wss
    @11
    @3
    wss
    @10
    cA
    onssr1
    cA
    @2
    rankssb
    sylc
    eqsstr3d
    eqssd
    @4
    cA
    @3
    @0
    @4
    id
    @2
    rankdmr1
    syl6eqelr
    impbii
end
