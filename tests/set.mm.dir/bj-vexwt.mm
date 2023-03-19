include "wal.mm"
include "wsb.mm"
include "cv.mm"
include "cab.mm"
include "wcel.mm"
include "stdpc4.mm"
include "df-clab.mm"
include "sylibr.mm"

theorem bj-vexwt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


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
    stdpc4
    wph
    vy
    vx
    df-clab
    sylibr
end
