include "con0.mm"
include "wrex.mm"
include "crab.mm"
include "cint.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "rabn0.mm"
include "wss.mm"
include "ssrab2.mm"
include "onint.mm"
include "mpan.mm"
include "sylbir.mm"
include "nfrab1.mm"
include "nfint.mm"
include "nfcv.mm"
include "elrabf.mm"
include "simprbi.mm"
include "syl.mm"

theorem onminsb
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume onminsb.1: |- F/ x ps
  assume onminsb.2: |- ( x = |^| { x e. On | ph } -> ( ph <-> ps ) )


  assert |- ( E. x e. On ph -> ps )

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
    wps
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
    @4
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
    wps
    wph
    wps
    vx
    @2
    con0
    vx
    @1
    wph
    vx
    con0
    nfrab1
    nfint
    vx
    con0
    nfcv
    onminsb.1
    onminsb.2
    elrabf
    simprbi
    syl
end
