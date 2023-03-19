include "wal.mm"
include "wsb.mm"
include "stdpc4.mm"
include "alimi.mm"
include "syl.mm"

theorem 2stdpc4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( A. x A. y ph -> [ z / x ] [ w / y ] ph )

  proof
    wph
    vy
    wal
    #
    vx
    wal
    wph
    vy
    vw
    wsb
    #
    vx
    wal
    @1
    vx
    vz
    wsb
    @0
    @1
    vx
    wph
    vy
    vw
    stdpc4
    alimi
    @1
    vx
    vz
    stdpc4
    syl
end
