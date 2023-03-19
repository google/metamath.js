include "wi.mm"
include "wex.mm"
include "wal.mm"
include "19.36v.mm"
include "mpbi.mm"

theorem 19.36iv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.36iv.1: |- E. x ( ph -> ps )

  disjoint ps x
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
    19.36iv.1
    wph
    wps
    vx
    19.36v
    mpbi
end
