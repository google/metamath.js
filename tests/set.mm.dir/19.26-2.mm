include "wa.mm"
include "wal.mm"
include "19.26.mm"
include "albii.mm"
include "bitri.mm"

theorem 19.26-2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x A. y ( ph /\ ps ) <-> ( A. x A. y ph /\ A. x A. y ps ) )

  proof
    wph
    wps
    wa
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
    vy
    wal
    #
    wa
    #
    vx
    wal
    @1
    vx
    wal
    @2
    vx
    wal
    wa
    @0
    @3
    vx
    wph
    wps
    vy
    19.26
    albii
    @1
    @2
    vx
    19.26
    bitri
end
