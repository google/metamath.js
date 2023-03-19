include "cep.mm"
include "wfr.mm"
include "cv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "dfepfr.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "zfreg.mm"
include "mpan.mm"
include "incom.mm"
include "eqeq1i.mm"
include "rexbii.mm"
include "sylib.mm"
include "adantl.mm"
include "mpgbir.mm"

theorem zfregfr
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- _E Fr A

  proof
    cA
    cep
    wfr
    vx
    cv
    #
    cA
    wss
    #
    @0
    c0
    wne
    #
    wa
    @0
    vy
    cv
    #
    cin
    #
    c0
    wceq
    #
    vy
    @0
    wrex
    #
    wi
    vx
    vx
    vy
    cA
    dfepfr
    @2
    @6
    @1
    @2
    @3
    @0
    cin
    #
    c0
    wceq
    #
    vy
    @0
    wrex
    #
    @6
    @0
    cvv
    wcel
    @2
    @9
    vx
    vex
    vy
    @0
    cvv
    zfreg
    mpan
    @8
    @5
    vy
    @0
    @7
    @4
    c0
    @3
    @0
    incom
    eqeq1i
    rexbii
    sylib
    adantl
    mpgbir
end
