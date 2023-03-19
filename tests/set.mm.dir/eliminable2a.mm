include "cv.mm"
include "cab.mm"
include "dfcleq.mm"

theorem eliminable2a
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let wps: wff ps

  disjoint x z
  disjoint y z
  disjoint ph z
  disjoint ps z
  assert |- ( x = { y | ph } <-> A. z ( z e. x <-> z e. { y | ph } ) )

  proof
    vz
    vx
    cv
    wph
    vy
    cab
    dfcleq
end
