include "cab.mm"
include "cv.mm"
include "dfcleq.mm"

theorem eliminable2b
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let wps: wff ps

  disjoint x z
  disjoint y z
  disjoint ph z
  disjoint ps z
  assert |- ( { x | ph } = y <-> A. z ( z e. { x | ph } <-> z e. y ) )

  proof
    vz
    wph
    vx
    cab
    vy
    cv
    dfcleq
end
