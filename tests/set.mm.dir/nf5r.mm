include "wex.mm"
include "wnf.mm"
include "wal.mm"
include "19.8a.mm"
include "wi.mm"
include "df-nf.mm"
include "biimpi.mm"
include "syl5.mm"

theorem nf5r
  param wph: wff ph
  param vx: setvar x


  assert |- ( F/ x ph -> ( ph -> A. x ph ) )

  proof
    wph
    wph
    vx
    wex
    #
    wph
    vx
    wnf
    #
    wph
    vx
    wal
    #
    wph
    vx
    19.8a
    @1
    @0
    @2
    wi
    wph
    vx
    df-nf
    biimpi
    syl5
end
