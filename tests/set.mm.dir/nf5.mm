include "wnf.mm"
include "wex.mm"
include "wal.mm"
include "wi.mm"
include "df-nf.mm"
include "nfa1.mm"
include "19.23.mm"
include "bitr4i.mm"

theorem nf5
  let wph: wff ph
  let vx: setvar x


  assert |- ( F/ x ph <-> A. x ( ph -> A. x ph ) )

  proof
    wph
    vx
    wnf
    wph
    vx
    wex
    wph
    vx
    wal
    #
    wi
    wph
    @0
    wi
    vx
    wal
    wph
    vx
    df-nf
    wph
    @0
    vx
    wph
    vx
    nfa1
    19.23
    bitr4i
end
