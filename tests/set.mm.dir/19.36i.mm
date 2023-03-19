include "wi.mm"
include "wex.mm"
include "wal.mm"
include "19.36.mm"
include "mpbi.mm"

theorem 19.36i
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.36.1: |- F/ x ps
  assume 19.36i.2: |- E. x ( ph -> ps )


  assert |- ( A. x ph -> ps )

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
    wi
    19.36i.2
    wph
    wps
    vx
    19.36.1
    19.36
    mpbi
end
