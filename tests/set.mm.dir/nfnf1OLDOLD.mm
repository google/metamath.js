include "wnfOLD.mm"
include "wal.mm"
include "wi.mm"
include "df-nfOLD.mm"
include "nfa1OLDOLD.mm"
include "nfxfrOLD.mm"

theorem nfnf1OLDOLD
  let wph: wff ph
  let vx: setvar x


  assert |- nfOLD x nfOLD x ph

  proof
    wph
    vx
    wnfOLD
    wph
    wph
    vx
    wal
    wi
    #
    vx
    wal
    vx
    wph
    vx
    df-nfOLD
    @0
    vx
    nfa1OLDOLD
    nfxfrOLD
end
