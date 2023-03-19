include "wsb.mm"
include "wal.mm"
include "sbimi.mm"
include "hbsb2a.mm"
include "syl.mm"

theorem hbsb3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume hbsb3.1: |- ( ph -> A. y ph )


  assert |- ( [ y / x ] ph -> A. x [ y / x ] ph )

  proof
    wph
    vx
    vy
    wsb
    #
    wph
    vy
    wal
    #
    vx
    vy
    wsb
    @0
    vx
    wal
    wph
    @1
    vx
    vy
    hbsb3.1
    sbimi
    wph
    vx
    vy
    hbsb2a
    syl
end
