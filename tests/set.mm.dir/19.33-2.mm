include "wal.mm"
include "wo.mm"
include "orc.mm"
include "2alimi.mm"
include "olc.mm"
include "jaoi.mm"

theorem 19.33-2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A. x A. y ph \/ A. x A. y ps ) -> A. x A. y ( ph \/ ps ) )

  proof
    wph
    vy
    wal
    vx
    wal
    wph
    wps
    wo
    #
    vy
    wal
    vx
    wal
    wps
    vy
    wal
    vx
    wal
    wph
    @0
    vx
    vy
    wph
    wps
    orc
    2alimi
    wps
    @0
    vx
    vy
    wps
    wph
    olc
    2alimi
    jaoi
end
