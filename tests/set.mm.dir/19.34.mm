include "wal.mm"
include "wex.mm"
include "wo.mm"
include "19.2.mm"
include "orim1i.mm"
include "19.43.mm"
include "sylibr.mm"

theorem 19.34
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( ( A. x ph \/ E. x ps ) -> E. x ( ph \/ ps ) )

  proof
    wph
    vx
    wal
    #
    wps
    vx
    wex
    #
    wo
    wph
    vx
    wex
    #
    @1
    wo
    wph
    wps
    wo
    vx
    wex
    @0
    @2
    @1
    wph
    vx
    19.2
    orim1i
    wph
    wps
    vx
    19.43
    sylibr
end
