include "wal.mm"
include "wo.mm"
include "orc.mm"
include "alimi.mm"
include "olc.mm"
include "jaoi.mm"

theorem 19.33
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( ( A. x ph \/ A. x ps ) -> A. x ( ph \/ ps ) )

  proof
    wph
    vx
    wal
    wph
    wps
    wo
    #
    vx
    wal
    wps
    vx
    wal
    wph
    @0
    vx
    wph
    wps
    orc
    alimi
    wps
    @0
    vx
    wps
    wph
    olc
    alimi
    jaoi
end
