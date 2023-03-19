include "wnf.mm"
include "wex.mm"
include "wal.mm"
include "wi.mm"
include "df-nf.mm"
include "nfe1.mm"
include "19.21.mm"
include "bitr4i.mm"

theorem nf6
  let wph: wff ph
  let vx: setvar x


  assert |- ( F/ x ph <-> A. x ( E. x ph -> ph ) )

  proof
    wph
    vx
    wnf
    wph
    vx
    wex
    #
    wph
    vx
    wal
    wi
    @0
    wph
    wi
    vx
    wal
    wph
    vx
    df-nf
    @0
    wph
    vx
    wph
    vx
    nfe1
    19.21
    bitr4i
end
