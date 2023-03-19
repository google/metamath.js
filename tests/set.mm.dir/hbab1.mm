include "cv.mm"
include "cab.mm"
include "wcel.mm"
include "wsb.mm"
include "df-clab.mm"
include "hbs1.mm"
include "hbxfrbi.mm"

theorem hbab1
  param wph: wff ph
  param vx: setvar x
  param vy: setvar y

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
    hbs1
    hbxfrbi
end
