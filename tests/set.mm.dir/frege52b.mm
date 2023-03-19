include "weq.mm"
include "cv.mm"
include "wsbc.mm"
include "wsb.mm"
include "ax-frege52c.mm"
include "sbsbc.mm"
include "3imtr4g.mm"

theorem frege52b
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( x = y -> ( [ x / z ] ph -> [ y / z ] ph ) )

  proof
    vx
    vy
    weq
    wph
    vz
    vx
    cv
    #
    wsbc
    wph
    vz
    vy
    cv
    #
    wsbc
    wph
    vz
    vx
    wsb
    wph
    vz
    vy
    wsb
    wph
    vz
    @0
    @1
    ax-frege52c
    wph
    vz
    vx
    sbsbc
    wph
    vz
    vy
    sbsbc
    3imtr4g
end
