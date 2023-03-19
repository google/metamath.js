include "wi.mm"
include "wal.mm"
include "19.21v.mm"
include "albii.mm"
include "bitri.mm"

theorem 19.21vv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y

  disjoint ps x
  disjoint ps y
  assert |- ( A. x A. y ( ps -> ph ) <-> ( ps -> A. x A. y ph ) )

  proof
    wps
    wph
    wi
    vy
    wal
    #
    vx
    wal
    wps
    wph
    vy
    wal
    #
    wi
    #
    vx
    wal
    wps
    @1
    vx
    wal
    wi
    @0
    @2
    vx
    wps
    wph
    vy
    19.21v
    albii
    wps
    @1
    vx
    19.21v
    bitri
end
