include "wsb.mm"
include "wal.mm"
include "sbimi.mm"
include "bj-hbsb2av.mm"
include "syl.mm"

theorem bj-hbsb3v
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume bj-hbsb3v.1: |- ( ph -> A. y ph )

  disjoint x y
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
    bj-hbsb3v.1
    sbimi
    wph
    vx
    vy
    bj-hbsb2av
    syl
end
