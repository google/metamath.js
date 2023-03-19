include "csur.mm"
include "con0.mm"
include "cbday.mm"
include "wfo.mm"
include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "cv.mm"
include "cdm.mm"
include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "dmexg.mm"
include "rgen.mm"
include "df-bday.mm"
include "mptfng.mm"
include "mpbi.mm"
include "wrex.mm"
include "cab.mm"
include "rnmpt.mm"
include "c1o.mm"
include "csn.mm"
include "cxp.mm"
include "noxp1o.mm"
include "c0.mm"
include "wne.mm"
include "1on.mm"
include "elexi.mm"
include "snnz.mm"
include "dmxp.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "dmeq.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "sylancl.mm"
include "wi.mm"
include "nodmon.mm"
include "eleq1a.mm"
include "syl.mm"
include "rexlimiv.mm"
include "impbii.mm"
include "abbi2i.mm"
include "eqtr4i.mm"
include "df-fo.mm"
include "mpbir2an.mm"

theorem bdayfo
  let vx: setvar x
  let vy: setvar y


  assert |- bday : No -onto-> On

  proof
    csur
    con0
    cbday
    wfo
    cbday
    csur
    wfn
    #
    cbday
    crn
    #
    con0
    wceq
    vx
    cv
    #
    cdm
    #
    cvv
    wcel
    #
    vx
    csur
    wral
    @0
    @4
    vx
    csur
    @2
    csur
    dmexg
    rgen
    vx
    csur
    @3
    cbday
    vx
    df-bday
    #
    mptfng
    mpbi
    @1
    vy
    cv
    #
    @3
    wceq
    #
    vx
    csur
    wrex
    #
    vy
    cab
    con0
    vx
    vy
    csur
    @3
    cbday
    @5
    rnmpt
    @8
    vy
    con0
    @6
    con0
    wcel
    #
    @8
    @9
    @6
    c1o
    csn
    #
    cxp
    #
    csur
    wcel
    @6
    @11
    cdm
    #
    wceq
    #
    @8
    @6
    noxp1o
    @12
    @6
    @10
    c0
    wne
    @12
    @6
    wceq
    c1o
    c1o
    con0
    1on
    elexi
    snnz
    @6
    @10
    dmxp
    ax-mp
    eqcomi
    @7
    @13
    vx
    @11
    csur
    @2
    @11
    wceq
    @3
    @12
    @6
    @2
    @11
    dmeq
    eqeq2d
    rspcev
    sylancl
    @7
    @9
    vx
    csur
    @2
    csur
    wcel
    @3
    con0
    wcel
    @7
    @9
    wi
    @2
    nodmon
    @3
    con0
    @6
    eleq1a
    syl
    rexlimiv
    impbii
    abbi2i
    eqtr4i
    csur
    con0
    cbday
    df-fo
    mpbir2an
end
