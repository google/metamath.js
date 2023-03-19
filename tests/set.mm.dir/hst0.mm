include "chst.mm"
include "wcel.mm"
include "c0h.mm"
include "cfv.mm"
include "chil.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "c0v.mm"
include "cch.mm"
include "h0elch.mm"
include "wa.mm"
include "cort.mm"
include "wss.mm"
include "helch.mm"
include "choccli.mm"
include "ch0lei.mm"
include "hstorth.mm"
include "mpanr12.mm"
include "mpan2.mm"
include "hstoh.mm"
include "mp3an2.mm"
include "mpdan.mm"

theorem hst0
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let cB: class B


  assert |- ( S e. CHStates -> ( S ` 0H ) = 0h )

  proof
    cS
    chst
    wcel
    #
    c0h
    cS
    cfv
    #
    chil
    cS
    cfv
    csp
    co
    cc0
    wceq
    #
    @1
    c0v
    wceq
    #
    @0
    c0h
    cch
    wcel
    #
    @2
    h0elch
    @0
    @4
    wa
    chil
    cch
    wcel
    c0h
    chil
    cort
    cfv
    #
    wss
    @2
    helch
    @5
    chil
    helch
    choccli
    ch0lei
    c0h
    chil
    cS
    hstorth
    mpanr12
    mpan2
    @0
    @4
    @2
    @3
    h0elch
    c0h
    cS
    hstoh
    mp3an2
    mpdan
end
