include "wex.mm"
include "wal.mm"
include "ax5e.mm"
include "ax-5.mm"
include "syl.mm"

theorem ax5ea
  param wph: wff ph
  param vx: setvar x

  disjoint ph x
  assert |- ( E. x ph -> A. x ph )

  proof
    wph
    vx
    wex
    wph
    wph
    vx
    wal
    wph
    vx
    ax5e
    wph
    vx
    ax-5
    syl
end
