include "con0.mm"
include "wrex.mm"
include "crab.mm"
include "cint.mm"
include "wcel.mm"
include "wsbc.mm"
include "c0.mm"
include "wne.mm"
include "rabn0.mm"
include "wss.mm"
include "ssrab2.mm"
include "onint.mm"
include "mpan.mm"
include "sylbir.mm"
include "nfcv.mm"
include "elrabsf.mm"
include "simprbi.mm"
include "syl.mm"

theorem onminesb
  let wph: wff ph
  let vx: setvar x


  assert |- ( E. x e. On ph -> [. |^| { x e. On | ph } / x ]. ph )

  proof
    wph
    vx
    con0
    wrex
    #
    wph
    vx
    con0
    crab
    #
    cint
    #
    @1
    wcel
    #
    wph
    vx
    @2
    wsbc
    #
    @0
    @1
    c0
    wne
    #
    @3
    wph
    vx
    con0
    rabn0
    @1
    con0
    wss
    @5
    @3
    wph
    vx
    con0
    ssrab2
    @1
    onint
    mpan
    sylbir
    @3
    @2
    con0
    wcel
    @4
    wph
    vx
    @2
    con0
    vx
    con0
    nfcv
    elrabsf
    simprbi
    syl
end
