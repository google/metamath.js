include "nfv.mm"
include "euan.mm"

theorem euanv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x

  disjoint ph x
  assert |- ( E! x ( ph /\ ps ) <-> ( ph /\ E! x ps ) )

  proof
    wph
    wps
    vx
    wph
    vx
    nfv
    euan
end
