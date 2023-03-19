include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wsb.mm"
include "wi.mm"
include "sb4.mm"
include "sb2.mm"
include "impbid1.mm"

theorem sb4b
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( -. A. x x = y -> ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) )

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
    wi
    vx
    wal
    wph
    vx
    vy
    sb4
    wph
    vx
    vy
    sb2
    impbid1
end
