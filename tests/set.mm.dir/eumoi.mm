include "weu.mm"
include "wmo.mm"
include "eumo.mm"
include "ax-mp.mm"

theorem eumoi
  let wph: wff ph
  let vx: setvar x
  assume eumoi.1: |- E! x ph


  assert |- E* x ph

  proof
    wph
    vx
    weu
    wph
    vx
    wmo
    eumoi.1
    wph
    vx
    eumo
    ax-mp
end
