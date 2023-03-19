include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "crest.mm"
include "co.mm"
include "wceq.mm"
include "wss.mm"
include "ssid.mm"
include "bj-restsnss.mm"
include "mpan2.mm"
include "wn.mm"
include "c0.mm"
include "cv.mm"
include "cin.mm"
include "cmpt.mm"
include "crn.mm"
include "df-rest.mm"
include "reldmmpt2.mm"
include "ovprc2.mm"
include "snprc.mm"
include "biimpi.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem bj-restsnid
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( { A } |`t A ) = { A }

  proof
    cA
    cvv
    wcel
    #
    cA
    csn
    #
    cA
    crest
    co
    #
    @1
    wceq
    #
    @0
    cA
    cA
    wss
    @3
    cA
    ssid
    cA
    cvv
    cA
    bj-restsnss
    mpan2
    @0
    wn
    #
    @2
    c0
    @1
    @1
    cA
    crest
    vx
    vy
    cvv
    cvv
    vz
    vx
    cv
    vz
    cv
    vy
    cv
    cin
    cmpt
    crn
    crest
    vy
    vz
    vx
    df-rest
    reldmmpt2
    ovprc2
    @4
    @1
    c0
    wceq
    cA
    snprc
    biimpi
    eqtr4d
    pm2.61i
end
