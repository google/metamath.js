include "weu.mm"
include "wex.mm"
include "wmo.mm"
include "eu5.mm"
include "baibr.mm"

theorem exmoeu2
  let wph: wff ph
  let vx: setvar x


  assert |- ( E. x ph -> ( E* x ph <-> E! x ph ) )

  proof
    wph
    vx
    weu
    wph
    vx
    wex
    wph
    vx
    wmo
    wph
    vx
    eu5
    baibr
end
