include "wnfOLD.mm"
include "wn.mm"
include "nfnf1OLDOLD.mm"
include "wal.mm"
include "wi.mm"
include "df-nfOLD.mm"
include "hbnt.mm"
include "sylbi.mm"
include "nfdOLD.mm"

theorem nfntOLD
  let wph: wff ph
  let vx: setvar x


  assert |- ( nfOLD x ph -> nfOLD x -. ph )

  proof
    wph
    vx
    wnfOLD
    #
    wph
    wn
    #
    vx
    wph
    vx
    nfnf1OLDOLD
    @0
    wph
    wph
    vx
    wal
    wi
    vx
    wal
    @1
    @1
    vx
    wal
    wi
    wph
    vx
    df-nfOLD
    wph
    vx
    hbnt
    sylbi
    nfdOLD
end
