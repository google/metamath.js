include "wex.mm"
include "exlimiv.mm"
include "ax-mp.mm"

theorem exlimiiv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume exlimiv.1: |- ( ph -> ps )
  assume exlimiiv.2: |- E. x ph

  disjoint ps x
  assert |- ps

  proof
    wph
    vx
    wex
    wps
    exlimiiv.2
    wph
    wps
    vx
    exlimiv.1
    exlimiv
    ax-mp
end
