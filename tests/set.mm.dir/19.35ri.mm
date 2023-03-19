include "wi.mm"
include "wex.mm"
include "wal.mm"
include "19.35.mm"
include "mpbir.mm"

theorem 19.35ri
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.35ri.1: |- ( A. x ph -> E. x ps )


  assert |- E. x ( ph -> ps )

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
    19.35ri.1
    wph
    wps
    vx
    19.35
    mpbir
end
