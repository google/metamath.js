include "wnf.mm"
include "cab.mm"
include "c0.mm"
include "wceq.mm"
include "cvv.mm"
include "wo.mm"
include "nfv.mm"
include "dfnf5.mm"
include "mpbi.mm"

theorem ab0orv
  let wph: wff ph
  let vx: setvar x

  disjoint ph x
  assert |- ( { x | ph } = (/) \/ { x | ph } = _V )

  proof
    wph
    vx
    wnf
    wph
    vx
    cab
    #
    c0
    wceq
    @0
    cvv
    wceq
    wo
    wph
    vx
    nfv
    wph
    vx
    dfnf5
    mpbi
end
