include "cv.mm"
include "cab.mm"
include "wcel.mm"
include "bj-vexwvt.mm"
include "mpg.mm"

theorem bj-vexwv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume bj-vexwv.1: |- ph

  disjoint x y
  assert |- y e. { x | ph }

  proof
    wph
    vy
    cv
    wph
    vx
    cab
    wcel
    vx
    wph
    vx
    vy
    bj-vexwvt
    bj-vexwv.1
    mpg
end
