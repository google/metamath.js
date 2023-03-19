include "cab.mm"
include "df-clel.mm"

theorem eliminable3b
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x z
  disjoint y z
  disjoint ph z
  disjoint ps z
  assert |- ( { x | ph } e. { y | ps } <-> E. z ( z = { x | ph } /\ z e. { y | ps } ) )

  proof
    vz
    wph
    vx
    cab
    wps
    vy
    cab
    df-clel
end
