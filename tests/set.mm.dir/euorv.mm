include "nfv.mm"
include "euor.mm"

theorem euorv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x

  disjoint ph x
  assert |- ( ( -. ph /\ E! x ps ) -> E! x ( ph \/ ps ) )

  proof
    wph
    wps
    vx
    wph
    vx
    nfv
    euor
end
