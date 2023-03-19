include "cv.mm"
include "cab.mm"
include "wcel.mm"
include "bj-vexwt.mm"
include "mpg.mm"

theorem bj-vexw
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume bj-vexw.1: |- ph


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
    bj-vexwt
    bj-vexw.1
    mpg
end
