include "wnfOLD.mm"
include "wal.mm"
include "wi.mm"
include "df-nfOLD.mm"
include "sp.mm"
include "sylbi.mm"

theorem nfrOLD
  let wph: wff ph
  let vx: setvar x


  assert |- ( nfOLD x ph -> ( ph -> A. x ph ) )

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
    @0
    wph
    vx
    df-nfOLD
    @0
    vx
    sp
    sylbi
end
