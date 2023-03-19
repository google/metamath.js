include "con0.mm"
include "wcel.mm"
include "ccf.mm"
include "cfv.mm"
include "wceq.mm"
include "wss.mm"
include "cfle.mm"
include "a1i.mm"
include "cv.mm"
include "wf.mm"
include "wsmo.mm"
include "wrex.mm"
include "wral.mm"
include "w3a.mm"
include "wex.mm"
include "cfsmo.mm"
include "wi.mm"
include "cfon.mm"
include "cfcoflem.mm"
include "mpan2.mm"
include "mpd.mm"
include "eqssd.mm"
include "wn.mm"
include "c0.mm"
include "cf0.mm"
include "cdm.mm"
include "cff.mm"
include "fdmi.mm"
include "eleq2i.mm"
include "ndmfv.mm"
include "sylnbir.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem cfidm
  let cA: class A
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y


  assert |- ( cf ` ( cf ` A ) ) = ( cf ` A )

  proof
    cA
    con0
    wcel
    #
    cA
    ccf
    cfv
    #
    ccf
    cfv
    #
    @1
    wceq
    @0
    @2
    @1
    @2
    @1
    wss
    @0
    @1
    cfle
    a1i
    @0
    @1
    cA
    vf
    cv
    #
    wf
    @3
    wsmo
    vx
    cv
    vy
    cv
    @3
    cfv
    wss
    vy
    @1
    wrex
    vx
    cA
    wral
    w3a
    vf
    wex
    #
    @1
    @2
    wss
    #
    vx
    vy
    cA
    vf
    cfsmo
    @0
    @1
    con0
    wcel
    @4
    @5
    wi
    cA
    cfon
    vx
    vy
    cA
    @1
    vf
    cfcoflem
    mpan2
    mpd
    eqssd
    @0
    wn
    #
    c0
    ccf
    cfv
    c0
    @2
    @1
    cf0
    @6
    @1
    c0
    ccf
    @0
    cA
    ccf
    cdm
    #
    wcel
    @1
    c0
    wceq
    @7
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
    #
    fveq2d
    @8
    3eqtr4a
    pm2.61i
end
