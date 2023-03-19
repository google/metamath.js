include "wal.mm"
include "wi.mm"
include "ax-5.mm"
include "a1i.mm"

theorem ax5d
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x

  disjoint ps x
  assert |- ( ph -> ( ps -> A. x ps ) )

  proof
    wps
    wps
    vx
    wal
    wi
    wph
    wps
    vx
    ax-5
    a1i
end
