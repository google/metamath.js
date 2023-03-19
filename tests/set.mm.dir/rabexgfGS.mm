include "wcel.mm"
include "crab.mm"
include "wss.mm"
include "cvv.mm"
include "cv.mm"
include "wi.mm"
include "nfrab1.mm"
include "dfss2f.mm"
include "rabid.mm"
include "simplbi.mm"
include "mpgbir.mm"
include "elex.mm"
include "ssexg.mm"
include "sylancr.mm"

theorem rabexgfGS
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume rabexgfGS.1: |- F/_ x A


  assert |- ( A e. V -> { x e. A | ph } e. _V )

  proof
    cA
    cV
    wcel
    wph
    vx
    cA
    crab
    #
    cA
    wss
    #
    cA
    cvv
    wcel
    @0
    cvv
    wcel
    @1
    vx
    cv
    #
    @0
    wcel
    #
    @2
    cA
    wcel
    #
    wi
    vx
    vx
    @0
    cA
    wph
    vx
    cA
    nfrab1
    rabexgfGS.1
    dfss2f
    @3
    @4
    wph
    wph
    vx
    cA
    rabid
    simplbi
    mpgbir
    cA
    cV
    elex
    @0
    cA
    cvv
    ssexg
    sylancr
end
