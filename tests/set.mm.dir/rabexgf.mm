include "crab.mm"
include "wss.mm"
include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "wa.mm"
include "cab.mm"
include "df-rab.mm"
include "simpl.mm"
include "ss2abi.mm"
include "abid2f.mm"
include "sseqtri.mm"
include "eqsstri.mm"
include "ssexg.mm"
include "mpan.mm"

theorem rabexgf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume rabexgf.1: |- F/_ x A


  assert |- ( A e. V -> { x e. A | ph } e. _V )

  proof
    wph
    vx
    cA
    crab
    #
    cA
    wss
    cA
    cV
    wcel
    @0
    cvv
    wcel
    @0
    vx
    cv
    cA
    wcel
    #
    wph
    wa
    #
    vx
    cab
    #
    cA
    wph
    vx
    cA
    df-rab
    @3
    @1
    vx
    cab
    cA
    @2
    @1
    vx
    @1
    wph
    simpl
    ss2abi
    vx
    cA
    rabexgf.1
    abid2f
    sseqtri
    eqsstri
    @0
    cA
    cV
    ssexg
    mpan
end
