include "ax-5.mm"
include "hban.mm"

theorem bnj1351
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume bnj1351.1: |- ( ph -> A. x ph )

  disjoint ps x
  assert |- ( ( ph /\ ps ) -> A. x ( ph /\ ps ) )

  proof
    wph
    wps
    vx
    bnj1351.1
    wps
    vx
    ax-5
    hban
end
