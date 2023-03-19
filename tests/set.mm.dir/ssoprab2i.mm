include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "coprab.mm"
include "anim2i.mm"
include "2eximi.mm"
include "ssopab2i.mm"
include "dfoprab2.mm"
include "3sstr4i.mm"

theorem ssoprab2i
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume ssoprab2i.1: |- ( ph -> ps )

  disjoint x z
  disjoint y z
  disjoint ph w
  disjoint ps w
  disjoint w x
  disjoint w z
  disjoint w y
  assert |- { <. <. x , y >. , z >. | ph } C_ { <. <. x , y >. , z >. | ps }

  proof
    vw
    cv
    vx
    cv
    vy
    cv
    cop
    wceq
    #
    wph
    wa
    #
    vy
    wex
    vx
    wex
    #
    vw
    vz
    copab
    @0
    wps
    wa
    #
    vy
    wex
    vx
    wex
    #
    vw
    vz
    copab
    wph
    vx
    vy
    vz
    coprab
    wps
    vx
    vy
    vz
    coprab
    @2
    @4
    vw
    vz
    @1
    @3
    vx
    vy
    wph
    wps
    @0
    ssoprab2i.1
    anim2i
    2eximi
    ssopab2i
    wph
    vx
    vy
    vz
    vw
    dfoprab2
    wps
    vx
    vy
    vz
    vw
    dfoprab2
    3sstr4i
end
