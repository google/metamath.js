include "wex.mm"
include "wi.mm"
include "wn.mm"
include "wal.mm"
include "ax-5.mm"
include "eximal.mm"
include "mpbir.mm"

theorem ax5e
  param wph: wff ph
  param vx: setvar x

  disjoint ph x
  assert |- ( E. x ph -> ph )

  proof
    wph
    vx
    wex
    wph
    wi
    wph
    wn
    #
    @0
    vx
    wal
    wi
    @0
    vx
    ax-5
    wph
    wph
    vx
    eximal
    mpbir
end
