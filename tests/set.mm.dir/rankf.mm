include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "crnk.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "cvv.mm"
include "csuc.mm"
include "crab.mm"
include "cint.mm"
include "df-rank.mm"
include "funmpt2.mm"
include "copab.mm"
include "cmpt.mm"
include "mptv.mm"
include "eqtri.mm"
include "dmeqi.mm"
include "wex.mm"
include "cab.mm"
include "dmopab.mm"
include "wb.mm"
include "abeq1.mm"
include "wrex.mm"
include "rankwflemb.mm"
include "intexrab.mm"
include "isset.mm"
include "3bitrri.mm"
include "mpgbir.mm"
include "df-fn.mm"
include "mpbir2an.mm"
include "c0.mm"
include "wne.mm"
include "rabn0.mm"
include "bitr4i.mm"
include "intex.mm"
include "vex.mm"
include "fvmpt2.mm"
include "mpan.mm"
include "sylbi.mm"
include "wss.mm"
include "ssrab2.mm"
include "oninton.mm"
include "eqeltrd.mm"
include "rgen.mm"
include "ffnfv.mm"

theorem rankf
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- rank : U. ( R1 " On ) --> On

  proof
    cr1
    con0
    cima
    cuni
    #
    con0
    crnk
    wf
    crnk
    @0
    wfn
    #
    vx
    cv
    #
    crnk
    cfv
    #
    con0
    wcel
    #
    vx
    @0
    wral
    @1
    crnk
    wfun
    crnk
    cdm
    #
    @0
    wceq
    vx
    cvv
    @2
    vy
    cv
    csuc
    cr1
    cfv
    wcel
    #
    vy
    con0
    crab
    #
    cint
    #
    crnk
    vx
    vy
    df-rank
    #
    funmpt2
    @5
    vz
    cv
    @8
    wceq
    #
    vx
    vz
    copab
    #
    cdm
    #
    @0
    crnk
    @11
    crnk
    vx
    cvv
    @8
    cmpt
    @11
    @9
    vx
    vz
    @8
    mptv
    eqtri
    dmeqi
    @12
    @10
    vz
    wex
    #
    vx
    cab
    #
    @0
    @10
    vx
    vz
    dmopab
    @14
    @0
    wceq
    @13
    @2
    @0
    wcel
    #
    wb
    vx
    @13
    vx
    @0
    abeq1
    @15
    @6
    vy
    con0
    wrex
    #
    @8
    cvv
    wcel
    #
    @13
    vy
    @2
    rankwflemb
    #
    @6
    vy
    con0
    intexrab
    vz
    @8
    isset
    3bitrri
    mpgbir
    eqtri
    eqtri
    crnk
    @0
    df-fn
    mpbir2an
    @4
    vx
    @0
    @15
    @7
    c0
    wne
    #
    @4
    @15
    @16
    @19
    @18
    @6
    vy
    con0
    rabn0
    bitr4i
    @19
    @3
    @8
    con0
    @19
    @17
    @3
    @8
    wceq
    #
    @7
    intex
    @2
    cvv
    wcel
    @17
    @20
    vx
    vex
    vx
    cvv
    @8
    cvv
    crnk
    @9
    fvmpt2
    mpan
    sylbi
    @7
    con0
    wss
    @19
    @8
    con0
    wcel
    @6
    vy
    con0
    ssrab2
    @7
    oninton
    mpan
    eqeltrd
    sylbi
    rgen
    vx
    @0
    con0
    crnk
    ffnfv
    mpbir2an
end
