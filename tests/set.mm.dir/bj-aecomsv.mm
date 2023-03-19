include "weq.mm"
include "wal.mm"
include "bj-axc11nv.mm"
include "syl.mm"

theorem bj-aecomsv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume bj-aecomsv.1: |- ( A. x x = y -> ph )

  disjoint x y
  assert |- ( A. y y = x -> ph )

  proof
    vy
    vx
    weq
    vy
    wal
    vx
    vy
    weq
    vx
    wal
    wph
    vy
    vx
    bj-axc11nv
    bj-aecomsv.1
    syl
end
