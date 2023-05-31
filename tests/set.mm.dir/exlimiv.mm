include "wex.mm"
include "eximi.mm"
include "ax5e.mm"
include "syl.mm"

theorem exlimiv
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  assume exlimiv.1: |- ( ph -> ps )

  disjoint ps x
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
    exlimiv.1
    eximi
    wps
    vx
    ax5e
    syl
end
