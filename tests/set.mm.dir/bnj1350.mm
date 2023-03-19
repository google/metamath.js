include "ax-5.mm"
include "hb3an.mm"

theorem bnj1350
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume bnj1350.1: |- ( ch -> A. x ch )

  disjoint ph x
  disjoint ps x
  assert |- ( ( ph /\ ps /\ ch ) -> A. x ( ph /\ ps /\ ch ) )

  proof
    wph
    wps
    wch
    vx
    wph
    vx
    ax-5
    wps
    vx
    ax-5
    bnj1350.1
    hb3an
end
