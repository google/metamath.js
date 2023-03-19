include "wnfOLD.mm"
include "wex.mm"
include "wb.mm"
include "19.9tOLD.mm"
include "ax-mp.mm"

theorem 19.9OLD
  let wph: wff ph
  let vx: setvar x
  assume 19.9OLD.1: |- nfOLD x ph


  assert |- ( E. x ph <-> ph )

  proof
    wph
    vx
    wnfOLD
    wph
    vx
    wex
    wph
    wb
    19.9OLD.1
    wph
    vx
    19.9tOLD
    ax-mp
end
