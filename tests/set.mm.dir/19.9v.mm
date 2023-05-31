include "wex.mm"
include "ax5e.mm"
include "19.8v.mm"
include "impbii.mm"

theorem 19.9v
  param wph: wff ph
  param vx: setvar x

  disjoint ph x
  assert |- ( E. x ph <-> ph )

  proof
    wph
    vx
    wex
    wph
    wph
    vx
    ax5e
    wph
    vx
    19.8v
    impbii
end
