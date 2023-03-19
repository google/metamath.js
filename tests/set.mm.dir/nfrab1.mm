include "crab.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "df-rab.mm"
include "nfab1.mm"
include "nfcxfr.mm"

theorem nfrab1
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- F/_ x { x e. A | ph }

  proof
    vx
    wph
    vx
    cA
    crab
    vx
    cv
    cA
    wcel
    wph
    wa
    #
    vx
    cab
    wph
    vx
    cA
    df-rab
    @0
    vx
    nfab1
    nfcxfr
end
