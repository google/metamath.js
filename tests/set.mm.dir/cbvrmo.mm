include "wrex.mm"
include "wreu.mm"
include "wi.mm"
include "wrmo.mm"
include "cbvrex.mm"
include "cbvreu.mm"
include "imbi12i.mm"
include "rmo5.mm"
include "3bitr4i.mm"

theorem cbvrmo
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume cbvral.1: |- F/ y ph
  assume cbvral.2: |- F/ x ps
  assume cbvral.3: |- ( x = y -> ( ph <-> ps ) )

  disjoint A x
  disjoint A y
  disjoint x z
  disjoint A z
  disjoint y z
  disjoint ph z
  disjoint ps z
  assert |- ( E* x e. A ph <-> E* y e. A ps )

  proof
    wph
    vx
    cA
    wrex
    #
    wph
    vx
    cA
    wreu
    #
    wi
    wps
    vy
    cA
    wrex
    #
    wps
    vy
    cA
    wreu
    #
    wi
    wph
    vx
    cA
    wrmo
    wps
    vy
    cA
    wrmo
    @0
    @2
    @1
    @3
    wph
    wps
    vx
    vy
    cA
    cbvral.1
    cbvral.2
    cbvral.3
    cbvrex
    wph
    wps
    vx
    vy
    cA
    cbvral.1
    cbvral.2
    cbvral.3
    cbvreu
    imbi12i
    wph
    vx
    cA
    rmo5
    wps
    vy
    cA
    rmo5
    3bitr4i
end
