include "wal.mm"
include "wex.mm"
include "wi.mm"
include "wnf.mm"
include "ax-1.mm"
include "df-nf.mm"
include "sylibr.mm"

theorem nftht
  param wph: wff ph
  param vx: setvar x


  assert |- ( A. x ph -> F/ x ph )

  proof
    wph
    vx
    wal
    #
    wph
    vx
    wex
    #
    @0
    wi
    wph
    vx
    wnf
    @0
    @1
    ax-1
    wph
    vx
    df-nf
    sylibr
end
