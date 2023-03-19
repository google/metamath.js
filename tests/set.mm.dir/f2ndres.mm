include "cv.mm"
include "csn.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "cxp.mm"
include "wral.mm"
include "c2nd.mm"
include "cres.mm"
include "wf.mm"
include "cop.mm"
include "vex.mm"
include "op2nda.mm"
include "eleq1i.mm"
include "biimpri.mm"
include "adantl.mm"
include "rgen2.mm"
include "wceq.mm"
include "sneq.mm"
include "rneqd.mm"
include "unieqd.mm"
include "eleq1d.mm"
include "ralxp.mm"
include "mpbir.mm"
include "cvv.mm"
include "cmpt.mm"
include "df-2nd.mm"
include "reseq1i.mm"
include "wss.mm"
include "ssv.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "fmpt.mm"
include "mpbi.mm"

theorem f2ndres
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( 2nd |` ( A X. B ) ) : ( A X. B ) --> B

  proof
    vx
    cv
    #
    csn
    #
    crn
    #
    cuni
    #
    cB
    wcel
    #
    vx
    cA
    cB
    cxp
    #
    wral
    #
    @5
    cB
    c2nd
    @5
    cres
    #
    wf
    @6
    vy
    cv
    #
    vz
    cv
    #
    cop
    #
    csn
    #
    crn
    #
    cuni
    #
    cB
    wcel
    #
    vz
    cB
    wral
    vy
    cA
    wral
    @14
    vy
    vz
    cA
    cB
    @9
    cB
    wcel
    #
    @14
    @8
    cA
    wcel
    @14
    @15
    @13
    @9
    cB
    @8
    @9
    vy
    vex
    vz
    vex
    op2nda
    eleq1i
    biimpri
    adantl
    rgen2
    @4
    @14
    vx
    vy
    vz
    cA
    cB
    @0
    @10
    wceq
    #
    @3
    @13
    cB
    @16
    @2
    @12
    @16
    @1
    @11
    @0
    @10
    sneq
    rneqd
    unieqd
    eleq1d
    ralxp
    mpbir
    vx
    @5
    cB
    @3
    @7
    @7
    vx
    cvv
    @3
    cmpt
    #
    @5
    cres
    #
    vx
    @5
    @3
    cmpt
    #
    c2nd
    @17
    @5
    vx
    df-2nd
    reseq1i
    @5
    cvv
    wss
    @18
    @19
    wceq
    @5
    ssv
    vx
    cvv
    @5
    @3
    resmpt
    ax-mp
    eqtri
    fmpt
    mpbi
end
