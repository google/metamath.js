include "wex.mm"
include "ex.mm"
include "exlimd.mm"
include "mpd.mm"

theorem exlimdd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume exlimdd.1: |- F/ x ph
  assume exlimdd.2: |- F/ x ch
  assume exlimdd.3: |- ( ph -> E. x ps )
  assume exlimdd.4: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ph -> ch )

  proof
    wph
    wps
    vx
    wex
    wch
    exlimdd.3
    wph
    wps
    wch
    vx
    exlimdd.1
    exlimdd.2
    wph
    wps
    wch
    exlimdd.4
    ex
    exlimd
    mpd
end
