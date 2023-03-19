include "wa.mm"
include "wal.mm"
include "19.28v.mm"
include "albii.mm"
include "bitri.mm"

theorem 19.28vv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y

  disjoint ps x
  disjoint ps y
  assert |- ( A. x A. y ( ps /\ ph ) <-> ( ps /\ A. x A. y ph ) )

  proof
    wps
    wph
    wa
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
    wa
    #
    vx
    wal
    wps
    @1
    vx
    wal
    wa
    @0
    @2
    vx
    wps
    wph
    vy
    19.28v
    albii
    wps
    @1
    vx
    19.28v
    bitri
end
