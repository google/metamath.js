include "con0.mm"
include "wcel.mm"
include "cv.mm"
include "cin.mm"
include "wral.mm"
include "ctb.mm"
include "wa.mm"
include "wss.mm"
include "onelon.mm"
include "anim12dan.mm"
include "ex.mm"
include "onin.mm"
include "syl6.mm"
include "anc2ri.mm"
include "wi.mm"
include "inss1.mm"
include "jctl.mm"
include "adantr.mm"
include "a1i.mm"
include "ontr2.mm"
include "syl6c.mm"
include "ralrimivv.mm"
include "fiinbas.mm"
include "mpdan.mm"

theorem ontopbas
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( B e. On -> B e. TopBases )

  proof
    cB
    con0
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    cB
    wcel
    #
    vy
    cB
    wral
    vx
    cB
    wral
    cB
    ctb
    wcel
    @0
    @4
    vx
    vy
    cB
    cB
    @0
    @1
    cB
    wcel
    #
    @2
    cB
    wcel
    #
    wa
    #
    @3
    con0
    wcel
    #
    @0
    wa
    @3
    @1
    wss
    #
    @5
    wa
    #
    @4
    @0
    @7
    @8
    @0
    @7
    @1
    con0
    wcel
    #
    @2
    con0
    wcel
    #
    wa
    #
    @8
    @0
    @7
    @13
    @0
    @5
    @11
    @6
    @12
    cB
    @1
    onelon
    cB
    @2
    onelon
    anim12dan
    ex
    @1
    @2
    onin
    syl6
    anc2ri
    @7
    @10
    wi
    @0
    @5
    @10
    @6
    @5
    @9
    @1
    @2
    inss1
    jctl
    adantr
    a1i
    @3
    @1
    cB
    ontr2
    syl6c
    ralrimivv
    vx
    vy
    cB
    con0
    fiinbas
    mpdan
end
