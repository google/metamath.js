include "wex.mm"
include "ex.mm"
include "exlimdv.mm"
include "mpd.mm"

theorem exlimddv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume exlimddv.1: |- ( ph -> E. x ps )
  assume exlimddv.2: |- ( ( ph /\ ps ) -> ch )

  disjoint ch x
  disjoint ph x
  assert |- ( ph -> ch )

  proof
    wph
    wps
    vx
    wex
    wch
    exlimddv.1
    wph
    wps
    wch
    vx
    wph
    wps
    wch
    exlimddv.2
    ex
    exlimdv
    mpd
end
