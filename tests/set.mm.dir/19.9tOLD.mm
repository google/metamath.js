include "wnfOLD.mm"
include "wex.mm"
include "id.mm"
include "19.9dOLD.mm"
include "19.8a.mm"
include "impbid1.mm"

theorem 19.9tOLD
  let wph: wff ph
  let vx: setvar x


  assert |- ( nfOLD x ph -> ( E. x ph <-> ph ) )

  proof
    wph
    vx
    wnfOLD
    #
    wph
    vx
    wex
    wph
    wph
    @0
    vx
    @0
    id
    19.9dOLD
    wph
    vx
    19.8a
    impbid1
end
