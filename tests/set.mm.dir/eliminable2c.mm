include "cab.mm"
include "dfcleq.mm"

theorem eliminable2c
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x z
  disjoint y z
  disjoint ph z
  disjoint ps z
  assert |- ( { x | ph } = { y | ps } <-> A. z ( z e. { x | ph } <-> z e. { y | ps } ) )

  proof
    vz
    wph
    vx
    cab
    wps
    vy
    cab
    dfcleq
end
