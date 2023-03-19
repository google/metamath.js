include "weu.mm"
include "wmo.mm"
include "cab.mm"
include "cvv.mm"
include "wcel.mm"
include "eumo.mm"
include "moabex.mm"
include "syl.mm"

theorem euabex
  let wph: wff ph
  let vx: setvar x


  assert |- ( E! x ph -> { x | ph } e. _V )

  proof
    wph
    vx
    weu
    wph
    vx
    wmo
    wph
    vx
    cab
    cvv
    wcel
    wph
    vx
    eumo
    wph
    vx
    moabex
    syl
end
