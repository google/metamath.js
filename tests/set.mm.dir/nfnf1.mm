include "wnf.mm"
include "wex.mm"
include "wal.mm"
include "wi.mm"
include "df-nf.mm"
include "nfe1.mm"
include "nfa1.mm"
include "nfim.mm"
include "nfxfr.mm"

theorem nfnf1
  let wph: wff ph
  let vx: setvar x


  assert |- F/ x F/ x ph

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
    #
    wi
    vx
    wph
    vx
    df-nf
    @0
    @1
    vx
    wph
    vx
    nfe1
    wph
    vx
    nfa1
    nfim
    nfxfr
end
