include "con0.mm"
include "wcel.mm"
include "ccf.mm"
include "cfv.mm"
include "ccrd.mm"
include "wceq.mm"
include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "cint.mm"
include "cfval.mm"
include "c0.mm"
include "wne.mm"
include "vex.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "elab.mm"
include "fveq2.mm"
include "cardidm.mm"
include "syl6eq.mm"
include "eqeq2.mm"
include "mpbird.mm"
include "adantr.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "cardon.mm"
include "syl6eqelr.mm"
include "ssriv.mm"
include "cvv.mm"
include "fvex.mm"
include "intex.mm"
include "sylibr.mm"
include "onint.mm"
include "sylancr.mm"
include "eqeltrd.mm"
include "id.mm"
include "eqeq12d.mm"
include "vtoclga.mm"
include "syl.mm"
include "wn.mm"
include "cdm.mm"
include "cff.mm"
include "fdmi.mm"
include "eleq2i.mm"
include "ndmfv.mm"
include "sylnbir.mm"
include "card0.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem cardcf
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v


  assert |- ( card ` ( cf ` A ) ) = ( cf ` A )

  proof
    cA
    con0
    wcel
    #
    cA
    ccf
    cfv
    #
    ccrd
    cfv
    #
    @1
    wceq
    #
    @0
    @1
    vx
    cv
    #
    vy
    cv
    #
    ccrd
    cfv
    #
    wceq
    #
    @5
    cA
    wss
    vz
    cv
    vw
    cv
    wss
    vw
    @5
    wrex
    vz
    cA
    wral
    wa
    #
    wa
    #
    vy
    wex
    #
    vx
    cab
    #
    wcel
    @3
    @0
    @1
    @11
    cint
    #
    @11
    vx
    vy
    vz
    vw
    cA
    cfval
    #
    @0
    @11
    con0
    wss
    @11
    c0
    wne
    #
    @12
    @11
    wcel
    vv
    @11
    con0
    vv
    cv
    #
    @11
    wcel
    #
    @15
    @15
    ccrd
    cfv
    #
    con0
    @16
    @15
    @6
    wceq
    #
    @8
    wa
    #
    vy
    wex
    #
    @17
    @15
    wceq
    #
    @10
    @20
    vx
    @15
    vv
    vex
    @4
    @15
    wceq
    #
    @9
    @19
    vy
    @22
    @7
    @18
    @8
    @4
    @15
    @6
    eqeq1
    anbi1d
    exbidv
    elab
    @19
    @21
    vy
    @18
    @21
    @8
    @18
    @21
    @17
    @6
    wceq
    @18
    @17
    @6
    ccrd
    cfv
    @6
    @15
    @6
    ccrd
    fveq2
    @5
    cardidm
    syl6eq
    @15
    @6
    @17
    eqeq2
    mpbird
    adantr
    exlimiv
    sylbi
    #
    @15
    cardon
    syl6eqelr
    ssriv
    @0
    @12
    cvv
    wcel
    @14
    @0
    @12
    @1
    cvv
    @13
    cA
    ccf
    fvex
    syl6eqelr
    @11
    intex
    sylibr
    @11
    onint
    sylancr
    eqeltrd
    @21
    @3
    vv
    @1
    @11
    @15
    @1
    wceq
    #
    @17
    @2
    @15
    @1
    @15
    @1
    ccrd
    fveq2
    @24
    id
    eqeq12d
    @23
    vtoclga
    syl
    @0
    wn
    @1
    c0
    wceq
    #
    @3
    @0
    cA
    ccf
    cdm
    #
    wcel
    @25
    @26
    con0
    cA
    con0
    con0
    ccf
    cff
    fdmi
    eleq2i
    cA
    ccf
    ndmfv
    sylnbir
    @25
    c0
    ccrd
    cfv
    c0
    @2
    @1
    card0
    @1
    c0
    ccrd
    fveq2
    @25
    id
    3eqtr4a
    syl
    pm2.61i
end
