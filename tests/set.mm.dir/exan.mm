include "wex.mm"
include "wa.mm"
include "simpli.mm"
include "wi.mm"
include "simpri.mm"
include "pm3.21.mm"
include "ax-mp.mm"
include "eximi.mm"

theorem exan
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume exan.1: |- ( E. x ph /\ ps )


  assert |- E. x ( ph /\ ps )

  proof
    wph
    vx
    wex
    #
    wph
    wps
    wa
    #
    vx
    wex
    @0
    wps
    exan.1
    simpli
    wph
    @1
    vx
    wps
    wph
    @1
    wi
    @0
    wps
    exan.1
    simpri
    wps
    wph
    pm3.21
    ax-mp
    eximi
    ax-mp
end
