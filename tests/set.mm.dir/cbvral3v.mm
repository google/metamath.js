include "wral.mm"
include "weq.mm"
include "2ralbidv.mm"
include "cbvralv.mm"
include "cbvral2v.mm"
include "ralbii.mm"
include "bitri.mm"

theorem cbvral3v
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  assume cbvral3v.1: |- ( x = w -> ( ph <-> ch ) )
  assume cbvral3v.2: |- ( y = v -> ( ch <-> th ) )
  assume cbvral3v.3: |- ( z = u -> ( th <-> ps ) )

  disjoint ph w
  disjoint ps z
  disjoint ch x
  disjoint ch v
  disjoint u y
  disjoint th y
  disjoint th u
  disjoint A x
  disjoint A w
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint w y
  disjoint B w
  disjoint B v
  disjoint x z
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint w z
  disjoint C w
  disjoint v z
  disjoint C v
  disjoint C u
  assert |- ( A. x e. A A. y e. B A. z e. C ph <-> A. w e. A A. v e. B A. u e. C ps )

  proof
    wph
    vz
    cC
    wral
    vy
    cB
    wral
    #
    vx
    cA
    wral
    wch
    vz
    cC
    wral
    vy
    cB
    wral
    #
    vw
    cA
    wral
    wps
    vu
    cC
    wral
    vv
    cB
    wral
    #
    vw
    cA
    wral
    @0
    @1
    vx
    vw
    cA
    vx
    vw
    weq
    wph
    wch
    vy
    vz
    cB
    cC
    cbvral3v.1
    2ralbidv
    cbvralv
    @1
    @2
    vw
    cA
    wch
    wps
    wth
    vy
    vz
    vv
    vu
    cB
    cC
    cbvral3v.2
    cbvral3v.3
    cbvral2v
    ralbii
    bitri
end
