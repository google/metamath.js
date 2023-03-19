include "cxp.mm"
include "wrex.mm"
include "cv.mm"
include "csn.mm"
include "ciun.mm"
include "iunxpconst.mm"
include "rexeqi.mm"
include "rexiunxp.mm"
include "bitr3i.mm"

theorem rexxp
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
  assert |- ( E. x e. ( A X. B ) ph <-> E. y e. A E. z e. B ps )

  proof
    wph
    vx
    cA
    cB
    cxp
    #
    wrex
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
    wrex
    wps
    vz
    cB
    wrex
    vy
    cA
    wrex
    wph
    vx
    @1
    @0
    vy
    cA
    cB
    iunxpconst
    rexeqi
    wph
    wps
    vx
    vy
    vz
    cA
    cB
    ralxp.1
    rexiunxp
    bitr3i
end
