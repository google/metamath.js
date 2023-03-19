include "wal.mm"
include "wex.mm"
include "wa.mm"
include "19.29r.mm"
include "19.29.mm"
include "eximi.mm"
include "syl.mm"

theorem 19.29x
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( E. x A. y ph /\ A. x E. y ps ) -> E. x E. y ( ph /\ ps ) )

  proof
    wph
    vy
    wal
    #
    vx
    wex
    wps
    vy
    wex
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
    19.29
    eximi
    syl
end
