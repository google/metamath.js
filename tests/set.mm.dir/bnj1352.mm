include "ax-5.mm"
include "hban.mm"

theorem bnj1352
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume bnj1352.1: |- ( ps -> A. x ps )

  disjoint ph x
  assert |- ( ( ph /\ ps ) -> A. x ( ph /\ ps ) )

  proof
    wph
    wps
    vx
    wph
    vx
    ax-5
    bnj1352.1
    hban
end
