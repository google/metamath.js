include "wal.mm"
include "alimdh.mm"
include "ax-11.mm"
include "syl6.mm"

theorem hbald
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume hbald.1: |- ( ph -> A. y ph )
  assume hbald.2: |- ( ph -> ( ps -> A. x ps ) )


  assert |- ( ph -> ( A. y ps -> A. x A. y ps ) )

  proof
    wph
    wps
    vy
    wal
    #
    wps
    vx
    wal
    #
    vy
    wal
    @0
    vx
    wal
    wph
    wps
    @1
    vy
    hbald.1
    hbald.2
    alimdh
    wps
    vy
    vx
    ax-11
    syl6
end
