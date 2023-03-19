include "wal.mm"
include "weq.mm"
include "wi.mm"
include "wsb.mm"
include "ala1.mm"
include "sb2.mm"
include "syl.mm"

theorem stdpc4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x ph -> [ y / x ] ph )

  proof
    wph
    vx
    wal
    vx
    vy
    weq
    #
    wph
    wi
    vx
    wal
    wph
    vx
    vy
    wsb
    wph
    @0
    vx
    ala1
    wph
    vx
    vy
    sb2
    syl
end
