include "cvv.mm"
include "wrex.mm"
include "wsb.mm"
include "wex.mm"
include "cbvrexsv.mm"
include "rexv.mm"
include "3bitr3i.mm"

theorem cbvexsv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint ph y
  assert |- ( E. x ph <-> E. y [ y / x ] ph )

  proof
    wph
    vx
    cvv
    wrex
    wph
    vx
    vy
    wsb
    #
    vy
    cvv
    wrex
    wph
    vx
    wex
    @0
    vy
    wex
    wph
    vx
    vy
    cvv
    cbvrexsv
    wph
    vx
    rexv
    @0
    vy
    rexv
    3bitr3i
end
