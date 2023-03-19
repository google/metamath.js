include "wreu.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "weu.mm"
include "df-reu.mm"
include "nfeu1.mm"
include "nfxfr.mm"

theorem nfreu1
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- F/ x E! x e. A ph

  proof
    wph
    vx
    cA
    wreu
    vx
    cv
    cA
    wcel
    wph
    wa
    #
    vx
    weu
    vx
    wph
    vx
    cA
    df-reu
    @0
    vx
    nfeu1
    nfxfr
end
