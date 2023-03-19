include "wral.mm"
include "weq.mm"
include "ralbidv.mm"
include "cbvralv.mm"
include "ralbii.mm"
include "bitri.mm"

theorem cbvral2v
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  assume cbvral2v.1: |- ( x = z -> ( ph <-> ch ) )
  assume cbvral2v.2: |- ( y = w -> ( ch <-> ps ) )

  disjoint A x
  disjoint A z
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint y z
  disjoint B z
  disjoint B w
  disjoint ph z
  disjoint ps y
  disjoint ch x
  disjoint ch w
  assert |- ( A. x e. A A. y e. B ph <-> A. z e. A A. w e. B ps )

  proof
    wph
    vy
    cB
    wral
    #
    vx
    cA
    wral
    wch
    vy
    cB
    wral
    #
    vz
    cA
    wral
    wps
    vw
    cB
    wral
    #
    vz
    cA
    wral
    @0
    @1
    vx
    vz
    cA
    vx
    vz
    weq
    wph
    wch
    vy
    cB
    cbvral2v.1
    ralbidv
    cbvralv
    @1
    @2
    vz
    cA
    wch
    wps
    vy
    vw
    cB
    cbvral2v.2
    cbvralv
    ralbii
    bitri
end
