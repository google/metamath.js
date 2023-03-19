include "wo.mm"
include "wmo.mm"
include "moor.mm"
include "olc.mm"
include "moimi.mm"
include "jca.mm"

theorem mooran2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( E* x ( ph \/ ps ) -> ( E* x ph /\ E* x ps ) )

  proof
    wph
    wps
    wo
    #
    vx
    wmo
    wph
    vx
    wmo
    wps
    vx
    wmo
    wph
    wps
    vx
    moor
    wps
    @0
    vx
    wps
    wph
    olc
    moimi
    jca
end
