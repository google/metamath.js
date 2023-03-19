include "wi.mm"
include "wal.mm"
include "alim.mm"
include "mpg.mm"

theorem alimi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume alimi.1: |- ( ph -> ps )


  assert |- ( A. x ph -> A. x ps )

  proof
    wph
    wps
    wi
    wph
    vx
    wal
    wps
    vx
    wal
    wi
    vx
    wph
    wps
    vx
    alim
    alimi.1
    mpg
end
