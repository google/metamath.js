include "cab.mm"
include "cv.mm"
include "df-clel.mm"

theorem eliminable3a
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let wps: wff ps

  disjoint x z
  disjoint y z
  disjoint ph z
  disjoint ps z
  assert |- ( { x | ph } e. y <-> E. z ( z = { x | ph } /\ z e. y ) )

  proof
    vz
    wph
    vx
    cab
    vy
    cv
    df-clel
end
