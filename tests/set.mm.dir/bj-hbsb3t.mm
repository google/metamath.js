include "wal.mm"
include "wi.mm"
include "wsb.mm"
include "spsbim.mm"
include "hbsb2a.mm"
include "syl6.mm"

theorem bj-hbsb3t
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x ( ph -> A. y ph ) -> ( [ y / x ] ph -> A. x [ y / x ] ph ) )

  proof
    wph
    wph
    vy
    wal
    #
    wi
    vx
    wal
    wph
    vx
    vy
    wsb
    #
    @0
    vx
    vy
    wsb
    @1
    vx
    wal
    wph
    @0
    vx
    vy
    spsbim
    wph
    vx
    vy
    hbsb2a
    syl6
end
