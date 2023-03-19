include "wex.mm"
include "eximi.mm"
include "syl.mm"

theorem bj-exlime
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume bj-exlime.1: |- ( E. x ps -> ps )
  assume bj-exlime.2: |- ( ph -> ps )


  assert |- ( E. x ph -> ps )

  proof
    wph
    vx
    wex
    wps
    vx
    wex
    wps
    wph
    wps
    vx
    bj-exlime.2
    eximi
    bj-exlime.1
    syl
end
