include "wex.mm"
include "wa.mm"
include "ancli.mm"
include "nf5i.mm"
include "19.42-1.mm"
include "syl.mm"

theorem bnj596
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume bnj596.1: |- ( ph -> A. x ph )
  assume bnj596.2: |- ( ph -> E. x ps )


  assert |- ( ph -> E. x ( ph /\ ps ) )

  proof
    wph
    wph
    wps
    vx
    wex
    #
    wa
    wph
    wps
    wa
    vx
    wex
    wph
    @0
    bnj596.2
    ancli
    wph
    wps
    vx
    wph
    vx
    bnj596.1
    nf5i
    19.42-1
    syl
end
