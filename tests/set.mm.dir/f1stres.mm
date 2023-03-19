include "cv.mm"
include "csn.mm"
include "cdm.mm"
include "cuni.mm"
include "wcel.mm"
include "cxp.mm"
include "wral.mm"
include "c1st.mm"
include "cres.mm"
include "wf.mm"
include "cop.mm"
include "vex.mm"
include "op1sta.mm"
include "eleq1i.mm"
include "biimpri.mm"
include "adantr.mm"
include "rgen2.mm"
include "wceq.mm"
include "sneq.mm"
include "dmeqd.mm"
include "unieqd.mm"
include "eleq1d.mm"
include "ralxp.mm"
include "mpbir.mm"
include "cvv.mm"
include "cmpt.mm"
include "df-1st.mm"
include "reseq1i.mm"
include "wss.mm"
include "ssv.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "fmpt.mm"
include "mpbi.mm"

theorem f1stres
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( 1st |` ( A X. B ) ) : ( A X. B ) --> A

  proof
    vx
    cv
    #
    csn
    #
    cdm
    #
    cuni
    #
    cA
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
    cA
    c1st
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
    cdm
    #
    cuni
    #
    cA
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
    @8
    cA
    wcel
    #
    @14
    @9
    cB
    wcel
    @14
    @15
    @13
    @8
    cA
    @8
    @9
    vy
    vex
    vz
    vex
    op1sta
    eleq1i
    biimpri
    adantr
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
    cA
    @16
    @2
    @12
    @16
    @1
    @11
    @0
    @10
    sneq
    dmeqd
    unieqd
    eleq1d
    ralxp
    mpbir
    vx
    @5
    cA
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
    c1st
    @17
    @5
    vx
    df-1st
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
