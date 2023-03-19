include "con0.mm"
include "cv.mm"
include "ccrd.mm"
include "cfv.mm"
include "wceq.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "cint.mm"
include "ccf.mm"
include "df-cf.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cardon.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "adantr.mm"
include "exlimiv.mm"
include "abssi.mm"
include "cflem.mm"
include "abn0.mm"
include "sylibr.mm"
include "oninton.mm"
include "sylancr.mm"
include "fmpti.mm"

theorem cff
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v


  assert |- cf : On --> On

  proof
    vx
    con0
    con0
    vy
    cv
    #
    vz
    cv
    #
    ccrd
    cfv
    #
    wceq
    #
    @1
    vx
    cv
    #
    wss
    vw
    cv
    vv
    cv
    wss
    vv
    @1
    wrex
    vw
    @4
    wral
    wa
    #
    wa
    #
    vz
    wex
    #
    vy
    cab
    #
    cint
    #
    ccf
    vx
    vy
    vz
    vw
    vv
    df-cf
    @4
    con0
    wcel
    #
    @8
    con0
    wss
    @8
    c0
    wne
    #
    @9
    con0
    wcel
    @7
    vy
    con0
    @6
    @0
    con0
    wcel
    #
    vz
    @3
    @12
    @5
    @3
    @12
    @2
    con0
    wcel
    @1
    cardon
    @0
    @2
    con0
    eleq1
    mpbiri
    adantr
    exlimiv
    abssi
    @10
    @7
    vy
    wex
    @11
    vy
    vz
    vw
    vv
    @4
    con0
    cflem
    @7
    vy
    abn0
    sylibr
    @8
    oninton
    sylancr
    fmpti
end
