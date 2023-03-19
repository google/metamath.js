include "wal.mm"
include "wi.mm"
include "wex.mm"
include "exim.mm"
include "axc7e.mm"
include "syl6.mm"

theorem 19.9ht
  let wph: wff ph
  let vx: setvar x


  assert |- ( A. x ( ph -> A. x ph ) -> ( E. x ph -> ph ) )

  proof
    wph
    wph
    vx
    wal
    #
    wi
    vx
    wal
    wph
    vx
    wex
    @0
    vx
    wex
    wph
    wph
    @0
    vx
    exim
    wph
    vx
    axc7e
    syl6
end
