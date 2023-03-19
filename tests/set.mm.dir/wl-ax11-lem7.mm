include "weq.mm"
include "wal.mm"
include "wn.mm"
include "nfna1.mm"
include "19.28.mm"

theorem wl-ax11-lem7
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x ( -. A. x x = y /\ ph ) <-> ( -. A. x x = y /\ A. x ph ) )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    wn
    wph
    vx
    @0
    vx
    nfna1
    19.28
end
