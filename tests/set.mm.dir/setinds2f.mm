include "cv.mm"
include "wsbc.mm"
include "wral.mm"
include "wsb.mm"
include "sbsbc.mm"
include "sbie.mm"
include "bitr3i.mm"
include "ralbii.mm"
include "sylbi.mm"
include "setinds.mm"

theorem setinds2f
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume setinds2f.1: |- F/ x ps
  assume setinds2f.2: |- ( x = y -> ( ph <-> ps ) )
  assume setinds2f.3: |- ( A. y e. x ps -> ph )

  disjoint x y
  disjoint ph y
  assert |- ph

  proof
    wph
    vx
    vy
    wph
    vx
    vy
    cv
    wsbc
    #
    vy
    vx
    cv
    #
    wral
    wps
    vy
    @1
    wral
    wph
    @0
    wps
    vy
    @1
    @0
    wph
    vx
    vy
    wsb
    wps
    wph
    vx
    vy
    sbsbc
    wph
    wps
    vx
    vy
    setinds2f.1
    setinds2f.2
    sbie
    bitr3i
    ralbii
    setinds2f.3
    sylbi
    setinds
end
