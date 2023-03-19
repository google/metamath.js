include "wal.mm"
include "wsb.mm"
include "bj-stdpc4v.mm"
include "alimi.mm"
include "syl.mm"

theorem bj-2stdpc4v
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x z
  disjoint w y
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
    bj-stdpc4v
    alimi
    @1
    vx
    vz
    bj-stdpc4v
    syl
end
