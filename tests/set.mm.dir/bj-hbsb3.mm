include "wal.mm"
include "wi.mm"
include "wsb.mm"
include "bj-hbsb3t.mm"
include "mpg.mm"

theorem bj-hbsb3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume bj-hbsb3.1: |- ( ph -> A. y ph )


  assert |- ( [ y / x ] ph -> A. x [ y / x ] ph )

  proof
    wph
    wph
    vy
    wal
    wi
    wph
    vx
    vy
    wsb
    #
    @0
    vx
    wal
    wi
    vx
    wph
    vx
    vy
    bj-hbsb3t
    bj-hbsb3.1
    mpg
end
