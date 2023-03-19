include "con0.mm"
include "crab.mm"
include "cint.mm"
include "cvv.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "intex.mm"
include "wss.mm"
include "ssrab2.mm"
include "oninton.mm"
include "mpan.mm"
include "sylbir.mm"
include "elex.mm"
include "impbii.mm"

theorem onintrab
  let wph: wff ph
  let vx: setvar x


  assert |- ( |^| { x e. On | ph } e. _V <-> |^| { x e. On | ph } e. On )

  proof
    wph
    vx
    con0
    crab
    #
    cint
    #
    cvv
    wcel
    #
    @1
    con0
    wcel
    #
    @2
    @0
    c0
    wne
    #
    @3
    @0
    intex
    @0
    con0
    wss
    @4
    @3
    wph
    vx
    con0
    ssrab2
    @0
    oninton
    mpan
    sylbir
    @1
    con0
    elex
    impbii
end
