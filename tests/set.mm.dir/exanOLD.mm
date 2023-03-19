include "wex.mm"
include "wa.mm"
include "simpli.mm"
include "wi.mm"
include "pm3.21.mm"
include "aleximi.mm"
include "simpri.mm"
include "mpg.mm"
include "ax-mp.mm"

theorem exanOLD
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
    #
    @0
    wps
    exan.1
    simpli
    wps
    @0
    @2
    wi
    vx
    wps
    wph
    @1
    vx
    wps
    wph
    pm3.21
    aleximi
    @0
    wps
    exan.1
    simpri
    mpg
    ax-mp
end
