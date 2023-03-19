include "wsb.mm"
include "cv.mm"
include "wral.mm"
include "con0.mm"
include "wcel.mm"
include "sbie.mm"
include "ralbii.mm"
include "syl5bi.mm"
include "tfis.mm"

theorem tfis2f
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume tfis2f.1: |- F/ x ps
  assume tfis2f.2: |- ( x = y -> ( ph <-> ps ) )
  assume tfis2f.3: |- ( x e. On -> ( A. y e. x ps -> ph ) )

  disjoint ph y
  disjoint x y
  assert |- ( x e. On -> ph )

  proof
    wph
    vx
    vy
    wph
    vx
    vy
    wsb
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
    @1
    con0
    wcel
    wph
    @0
    wps
    vy
    @1
    wph
    wps
    vx
    vy
    tfis2f.1
    tfis2f.2
    sbie
    ralbii
    tfis2f.3
    syl5bi
    tfis
end
