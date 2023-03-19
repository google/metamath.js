include "cv.mm"
include "cab.mm"
include "wcel.mm"
include "wsb.mm"
include "df-clab.mm"
include "hbsb.mm"
include "hbxfrbi.mm"

theorem hbab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume hbab.1: |- ( ph -> A. x ph )

  disjoint x z
  assert |- ( z e. { y | ph } -> A. x z e. { y | ph } )

  proof
    vz
    cv
    wph
    vy
    cab
    wcel
    wph
    vy
    vz
    wsb
    vx
    wph
    vz
    vy
    df-clab
    wph
    vy
    vz
    vx
    hbab.1
    hbsb
    hbxfrbi
end
