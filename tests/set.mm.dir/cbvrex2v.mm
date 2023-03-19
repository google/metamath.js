include "wrex.mm"
include "weq.mm"
include "rexbidv.mm"
include "cbvrexv.mm"
include "rexbii.mm"
include "bitri.mm"

theorem cbvrex2v
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  assume cbvrex2v.1: |- ( x = z -> ( ph <-> ch ) )
  assume cbvrex2v.2: |- ( y = w -> ( ch <-> ps ) )

  disjoint A x
  disjoint A z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint x y
  disjoint B z
  disjoint y z
  disjoint ch w
  disjoint ch x
  disjoint ph z
  disjoint ps y
  assert |- ( E. x e. A E. y e. B ph <-> E. z e. A E. w e. B ps )

  proof
    wph
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    wch
    vy
    cB
    wrex
    #
    vz
    cA
    wrex
    wps
    vw
    cB
    wrex
    #
    vz
    cA
    wrex
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
    cbvrex2v.1
    rexbidv
    cbvrexv
    @1
    @2
    vz
    cA
    wch
    wps
    vy
    vw
    cB
    cbvrex2v.2
    cbvrexv
    rexbii
    bitri
end
