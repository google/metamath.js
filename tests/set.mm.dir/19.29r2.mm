include "wex.mm"
include "wal.mm"
include "wa.mm"
include "19.29r.mm"
include "eximi.mm"
include "syl.mm"

theorem 19.29r2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( E. x E. y ph /\ A. x A. y ps ) -> E. x E. y ( ph /\ ps ) )

  proof
    wph
    vy
    wex
    #
    vx
    wex
    wps
    vy
    wal
    #
    vx
    wal
    wa
    @0
    @1
    wa
    #
    vx
    wex
    wph
    wps
    wa
    vy
    wex
    #
    vx
    wex
    @0
    @1
    vx
    19.29r
    @2
    @3
    vx
    wph
    wps
    vy
    19.29r
    eximi
    syl
end
