include "wmo.mm"
include "wal.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "coprab.mm"
include "wfun.mm"
include "mosubopt.mm"
include "alrimiv.mm"
include "copab.mm"
include "dfoprab2.mm"
include "funeqi.mm"
include "funopab.mm"
include "bitr2i.mm"
include "sylib.mm"

theorem funoprabg
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ph w
  assert |- ( A. x A. y E* z ph -> Fun { <. <. x , y >. , z >. | ph } )

  proof
    wph
    vz
    wmo
    vy
    wal
    vx
    wal
    #
    vw
    cv
    #
    vx
    cv
    vy
    cv
    cop
    wceq
    wph
    wa
    vy
    wex
    vx
    wex
    #
    vz
    wmo
    #
    vw
    wal
    #
    wph
    vx
    vy
    vz
    coprab
    #
    wfun
    #
    @0
    @3
    vw
    wph
    vz
    vx
    vy
    @1
    mosubopt
    alrimiv
    @6
    @2
    vw
    vz
    copab
    #
    wfun
    @4
    @5
    @7
    wph
    vx
    vy
    vz
    vw
    dfoprab2
    funeqi
    @2
    vw
    vz
    funopab
    bitr2i
    sylib
end
