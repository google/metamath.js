include "wex.mm"
include "exlimi.mm"
include "ax-mp.mm"

theorem exlimii
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume exlimii.1: |- F/ x ps
  assume exlimii.2: |- ( ph -> ps )
  assume exlimii.3: |- E. x ph


  assert |- ps

  proof
    wph
    vx
    wex
    wps
    exlimii.3
    wph
    wps
    vx
    exlimii.1
    exlimii.2
    exlimi
    ax-mp
end
