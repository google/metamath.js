include "wa.mm"
include "wex.mm"
include "19.40.mm"
include "eximi.mm"
include "syl.mm"

theorem 19.40-2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( E. x E. y ( ph /\ ps ) -> ( E. x E. y ph /\ E. x E. y ps ) )

  proof
    wph
    wps
    wa
    vy
    wex
    #
    vx
    wex
    wph
    vy
    wex
    #
    wps
    vy
    wex
    #
    wa
    #
    vx
    wex
    @1
    vx
    wex
    @2
    vx
    wex
    wa
    @0
    @3
    vx
    wph
    wps
    vy
    19.40
    eximi
    @1
    @2
    vx
    19.40
    syl
end
