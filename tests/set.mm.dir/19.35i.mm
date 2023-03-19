include "wi.mm"
include "wex.mm"
include "wal.mm"
include "19.35.mm"
include "mpbi.mm"

theorem 19.35i
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.35i.1: |- E. x ( ph -> ps )


  assert |- ( A. x ph -> E. x ps )

  proof
    wph
    wps
    wi
    vx
    wex
    wph
    vx
    wal
    wps
    vx
    wex
    wi
    19.35i.1
    wph
    wps
    vx
    19.35
    mpbi
end
