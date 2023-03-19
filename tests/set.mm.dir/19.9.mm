include "wnf.mm"
include "wex.mm"
include "wb.mm"
include "19.9t.mm"
include "ax-mp.mm"

theorem 19.9
  let wph: wff ph
  let vx: setvar x
  assume 19.9.1: |- F/ x ph


  assert |- ( E. x ph <-> ph )

  proof
    wph
    vx
    wnf
    wph
    vx
    wex
    wph
    wb
    19.9.1
    wph
    vx
    19.9t
    ax-mp
end
