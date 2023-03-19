include "wnf.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wb.mm"
include "bj-equsal1t.mm"
include "ax-mp.mm"

theorem bj-equsal1ti
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume bj-equsal1ti.1: |- F/ x ph


  assert |- ( A. x ( x = y -> ph ) <-> ph )

  proof
    wph
    vx
    wnf
    vx
    vy
    weq
    wph
    wi
    vx
    wal
    wph
    wb
    bj-equsal1ti.1
    wph
    vx
    vy
    bj-equsal1t
    ax-mp
end
