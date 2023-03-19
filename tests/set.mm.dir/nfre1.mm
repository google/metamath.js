include "wrex.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "df-rex.mm"
include "nfe1.mm"
include "nfxfr.mm"

theorem nfre1
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- F/ x E. x e. A ph

  proof
    wph
    vx
    cA
    wrex
    vx
    cv
    cA
    wcel
    wph
    wa
    #
    vx
    wex
    vx
    wph
    vx
    cA
    df-rex
    @0
    vx
    nfe1
    nfxfr
end
