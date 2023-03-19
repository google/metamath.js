include "wo.mm"
include "wal.mm"
include "19.31v.mm"
include "albii.mm"
include "bitri.mm"

theorem 19.31vv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y

  disjoint ps x
  disjoint ps y
  assert |- ( A. x A. y ( ph \/ ps ) <-> ( A. x A. y ph \/ ps ) )

  proof
    wph
    wps
    wo
    vy
    wal
    #
    vx
    wal
    wph
    vy
    wal
    #
    wps
    wo
    #
    vx
    wal
    @1
    vx
    wal
    wps
    wo
    @0
    @2
    vx
    wph
    wps
    vy
    19.31v
    albii
    @1
    wps
    vx
    19.31v
    bitri
end
