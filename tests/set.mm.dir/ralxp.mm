include "cxp.mm"
include "wral.mm"
include "cv.mm"
include "csn.mm"
include "ciun.mm"
include "iunxpconst.mm"
include "raleqi.mm"
include "raliunxp.mm"
include "bitr3i.mm"

theorem ralxp
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  assume ralxp.1: |- ( x = <. y , z >. -> ( ph <-> ps ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B z
  disjoint ph y
  disjoint ph z
  disjoint ps x
  disjoint B y
  assert |- ( A. x e. ( A X. B ) ph <-> A. y e. A A. z e. B ps )

  proof
    wph
    vx
    cA
    cB
    cxp
    #
    wral
    wph
    vx
    vy
    cA
    vy
    cv
    csn
    cB
    cxp
    ciun
    #
    wral
    wps
    vz
    cB
    wral
    vy
    cA
    wral
    wph
    vx
    @1
    @0
    vy
    cA
    cB
    iunxpconst
    raleqi
    wph
    wps
    vx
    vy
    vz
    cA
    cB
    ralxp.1
    raliunxp
    bitr3i
end
