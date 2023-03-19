include "wal.mm"
include "wo.mm"
include "wex.mm"
include "wa.mm"
include "wi.mm"
include "pm3.21.mm"
include "aleximi.mm"
include "pm3.2.mm"
include "jaoa.mm"
include "orcoms.mm"
include "19.40.mm"
include "impbid1.mm"

theorem 19.40b
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( ( A. x ph \/ A. x ps ) -> ( ( E. x ph /\ E. x ps ) <-> E. x ( ph /\ ps ) ) )

  proof
    wph
    vx
    wal
    #
    wps
    vx
    wal
    #
    wo
    wph
    vx
    wex
    #
    wps
    vx
    wex
    #
    wa
    #
    wph
    wps
    wa
    #
    vx
    wex
    #
    @1
    @0
    @4
    @6
    wi
    @1
    @2
    @6
    @0
    @3
    wps
    wph
    @5
    vx
    wps
    wph
    pm3.21
    aleximi
    wph
    wps
    @5
    vx
    wph
    wps
    pm3.2
    aleximi
    jaoa
    orcoms
    wph
    wps
    vx
    19.40
    impbid1
end
