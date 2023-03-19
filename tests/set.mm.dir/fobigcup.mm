include "cvv.mm"
include "cbigcup.mm"
include "wfo.mm"
include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "cv.mm"
include "cuni.mm"
include "wcel.mm"
include "wral.mm"
include "uniexg.mm"
include "rgen.mm"
include "dfbigcup2.mm"
include "mptfng.mm"
include "mpbi.mm"
include "wrex.mm"
include "cab.mm"
include "rnmpt.mm"
include "vex.mm"
include "csn.mm"
include "snex.mm"
include "unisn.mm"
include "eqcomi.mm"
include "unieq.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mp2an.mm"
include "2th.mm"
include "abbi2i.mm"
include "eqtr4i.mm"
include "df-fo.mm"
include "mpbir2an.mm"

theorem fobigcup
  let vx: setvar x
  let vy: setvar y


  assert |- Bigcup : _V -onto-> _V

  proof
    cvv
    cvv
    cbigcup
    wfo
    cbigcup
    cvv
    wfn
    #
    cbigcup
    crn
    #
    cvv
    wceq
    vx
    cv
    #
    cuni
    #
    cvv
    wcel
    #
    vx
    cvv
    wral
    @0
    @4
    vx
    cvv
    @2
    cvv
    uniexg
    rgen
    vx
    cvv
    @3
    cbigcup
    vx
    dfbigcup2
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
    cvv
    wrex
    #
    vy
    cab
    cvv
    vx
    vy
    cvv
    @3
    cbigcup
    @5
    rnmpt
    @8
    vy
    cvv
    @6
    cvv
    wcel
    @8
    vy
    vex
    #
    @6
    csn
    #
    cvv
    wcel
    @6
    @10
    cuni
    #
    wceq
    #
    @8
    @6
    snex
    @11
    @6
    @6
    @9
    unisn
    eqcomi
    @7
    @12
    vx
    @10
    cvv
    @2
    @10
    wceq
    @3
    @11
    @6
    @2
    @10
    unieq
    eqeq2d
    rspcev
    mp2an
    2th
    abbi2i
    eqtr4i
    cvv
    cvv
    cbigcup
    df-fo
    mpbir2an
end
