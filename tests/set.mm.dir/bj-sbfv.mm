include "wnf.mm"
include "wsb.mm"
include "wb.mm"
include "bj-sbftv.mm"
include "ax-mp.mm"

theorem bj-sbfv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume bj-sbfv.1: |- F/ x ph

  disjoint x y
  assert |- ( [ y / x ] ph <-> ph )

  proof
    wph
    vx
    wnf
    wph
    vx
    vy
    wsb
    wph
    wb
    bj-sbfv.1
    wph
    vx
    vy
    bj-sbftv
    ax-mp
end
