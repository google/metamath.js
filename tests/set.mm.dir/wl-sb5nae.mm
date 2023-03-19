include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wsb.mm"
include "wa.mm"
include "wex.mm"
include "sb1.mm"
include "sb3.mm"
include "impbid2.mm"

theorem wl-sb5nae
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( -. A. x x = y -> ( [ y / x ] ph <-> E. x ( x = y /\ ph ) ) )

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
    vy
    wsb
    @0
    wph
    wa
    vx
    wex
    wph
    vx
    vy
    sb1
    wph
    vx
    vy
    sb3
    impbid2
end
