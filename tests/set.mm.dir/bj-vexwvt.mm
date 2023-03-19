include "wal.mm"
include "wsb.mm"
include "cv.mm"
include "cab.mm"
include "wcel.mm"
include "bj-stdpc4v.mm"
include "df-clab.mm"
include "sylibr.mm"

theorem bj-vexwvt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( A. x ph -> y e. { x | ph } )

  proof
    wph
    vx
    wal
    wph
    vx
    vy
    wsb
    vy
    cv
    wph
    vx
    cab
    wcel
    wph
    vx
    vy
    bj-stdpc4v
    wph
    vy
    vx
    df-clab
    sylibr
end
