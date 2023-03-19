include "c0.mm"
include "crab.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "df-rab.mm"
include "wceq.mm"
include "wn.mm"
include "ab0.mm"
include "noel.mm"
include "intnanr.mm"
include "mpgbir.mm"
include "eqtri.mm"

theorem rab0
  let wph: wff ph
  let vx: setvar x


  assert |- { x e. (/) | ph } = (/)

  proof
    wph
    vx
    c0
    crab
    vx
    cv
    #
    c0
    wcel
    #
    wph
    wa
    #
    vx
    cab
    #
    c0
    wph
    vx
    c0
    df-rab
    @3
    c0
    wceq
    @2
    wn
    vx
    @2
    vx
    ab0
    @1
    wph
    @0
    noel
    intnanr
    mpgbir
    eqtri
end
