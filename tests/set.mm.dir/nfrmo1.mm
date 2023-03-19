include "wrmo.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "df-rmo.mm"
include "nfmo1.mm"
include "nfxfr.mm"

theorem nfrmo1
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- F/ x E* x e. A ph

  proof
    wph
    vx
    cA
    wrmo
    vx
    cv
    cA
    wcel
    wph
    wa
    #
    vx
    wmo
    vx
    wph
    vx
    cA
    df-rmo
    @0
    vx
    nfmo1
    nfxfr
end
