include "wo.mm"
include "wal.mm"
include "19.32v.mm"
include "orcom.mm"
include "albii.mm"
include "3bitr4i.mm"

theorem 19.31v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x

  disjoint ps x
  assert |- ( A. x ( ph \/ ps ) <-> ( A. x ph \/ ps ) )

  proof
    wps
    wph
    wo
    #
    vx
    wal
    wps
    wph
    vx
    wal
    #
    wo
    wph
    wps
    wo
    #
    vx
    wal
    @1
    wps
    wo
    wps
    wph
    vx
    19.32v
    @2
    @0
    vx
    wph
    wps
    orcom
    albii
    @1
    wps
    orcom
    3bitr4i
end
