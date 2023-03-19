include "ax5ea.mm"
include "nfi.mm"

theorem nfv
  let wph: wff ph
  let vx: setvar x

  disjoint ph x
  assert |- F/ x ph

  proof
    wph
    vx
    wph
    vx
    ax5ea
    nfi
end
