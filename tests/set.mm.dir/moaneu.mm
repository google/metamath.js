include "wmo.mm"
include "wa.mm"
include "weu.mm"
include "moanmo.mm"
include "eumo.mm"
include "anim2i.mm"
include "moimi.mm"
include "ax-mp.mm"

theorem moaneu
  let wph: wff ph
  let vx: setvar x


  assert |- E* x ( ph /\ E! x ph )

  proof
    wph
    wph
    vx
    wmo
    #
    wa
    #
    vx
    wmo
    wph
    wph
    vx
    weu
    #
    wa
    #
    vx
    wmo
    wph
    vx
    moanmo
    @3
    @1
    vx
    @2
    @0
    wph
    wph
    vx
    eumo
    anim2i
    moimi
    ax-mp
end
