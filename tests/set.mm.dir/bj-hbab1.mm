include "cv.mm"
include "cab.mm"
include "wcel.mm"
include "wsb.mm"
include "df-clab.mm"
include "bj-hbs1.mm"
include "hbxfrbi.mm"

theorem bj-hbab1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( y e. { x | ph } -> A. x y e. { x | ph } )

  proof
    vy
    cv
    wph
    vx
    cab
    wcel
    wph
    vx
    vy
    wsb
    vx
    wph
    vy
    vx
    df-clab
    wph
    vx
    vy
    bj-hbs1
    hbxfrbi
end
