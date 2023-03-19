include "cv.mm"
include "cc0.mm"
include "crusgr.mm"
include "wbr.mm"
include "cab.mm"
include "cvv.mm"
include "wnel.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "wceq.mm"
include "cvtx.mm"
include "wral.mm"
include "cusgr.mm"
include "crab.mm"
include "rgrusgrprc.mm"
include "wb.mm"
include "wcel.mm"
include "wa.mm"
include "cxnn0.mm"
include "w3a.mm"
include "vex.mm"
include "0xnn0.mm"
include "eqid.mm"
include "isrusgr0.mm"
include "mp2an.mm"
include "3ancomb.mm"
include "df-3an.mm"
include "mpbiran2.mm"
include "3bitri.mm"
include "abbii.mm"
include "df-rab.mm"
include "eqtr4i.mm"
include "neleq1.mm"
include "ax-mp.mm"
include "mpbir.mm"

theorem rusgrprc
  let vg: setvar g
  let ve: setvar e
  let vp: setvar p
  let vv: setvar v


  assert |- { g | g RegUSGraph 0 } e/ _V

  proof
    vg
    cv
    #
    cc0
    crusgr
    wbr
    #
    vg
    cab
    #
    cvv
    wnel
    #
    vv
    cv
    @0
    cvtxdg
    cfv
    #
    cfv
    cc0
    wceq
    vv
    @0
    cvtx
    cfv
    #
    wral
    #
    vg
    cusgr
    crab
    #
    cvv
    wnel
    #
    vv
    vg
    rgrusgrprc
    @2
    @7
    wceq
    @3
    @8
    wb
    @2
    @0
    cusgr
    wcel
    #
    @6
    wa
    #
    vg
    cab
    @7
    @1
    @10
    vg
    @1
    @9
    cc0
    cxnn0
    wcel
    #
    @6
    w3a
    #
    @9
    @6
    @11
    w3a
    #
    @10
    @0
    cvv
    wcel
    @11
    @1
    @12
    wb
    vg
    vex
    0xnn0
    vv
    @4
    @0
    cc0
    @5
    cvv
    cxnn0
    @5
    eqid
    @4
    eqid
    isrusgr0
    mp2an
    @9
    @11
    @6
    3ancomb
    @13
    @10
    @11
    0xnn0
    @9
    @6
    @11
    df-3an
    mpbiran2
    3bitri
    abbii
    @6
    vg
    cusgr
    df-rab
    eqtr4i
    @2
    @7
    cvv
    neleq1
    ax-mp
    mpbir
end
