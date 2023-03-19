include "wa.mm"
include "simpl.mm"
include "ax-mp.mm"

theorem simpli
  let wph: wff ph
  let wps: wff ps
  assume simpli.1: |- ( ph /\ ps )


  assert |- ph

  proof
    wph
    wps
    wa
    wph
    simpli.1
    wph
    wps
    simpl
    ax-mp
end
