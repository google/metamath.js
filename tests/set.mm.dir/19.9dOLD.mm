include "wal.mm"
include "wi.mm"
include "wex.mm"
include "wnfOLD.mm"
include "df-nfOLD.mm"
include "sylib.mm"
include "19.9ht.mm"
include "syl.mm"

theorem 19.9dOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.9dOLD.1: |- ( ps -> nfOLD x ph )


  assert |- ( ps -> ( E. x ph -> ph ) )

  proof
    wps
    wph
    wph
    vx
    wal
    wi
    vx
    wal
    #
    wph
    vx
    wex
    wph
    wi
    wps
    wph
    vx
    wnfOLD
    @0
    19.9dOLD.1
    wph
    vx
    df-nfOLD
    sylib
    wph
    vx
    19.9ht
    syl
end
