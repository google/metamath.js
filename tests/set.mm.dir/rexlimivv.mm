include "wrex.mm"
include "cv.mm"
include "wcel.mm"
include "rexlimdva.mm"
include "rexlimiv.mm"

theorem rexlimivv
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param vy: setvar y
  param cA: class A
  param cB: class B
  assume rexlimivv.1: |- ( ( x e. A /\ y e. B ) -> ( ph -> ps ) )

  disjoint x y
  disjoint ps x
  disjoint ps y
  disjoint A y
  assert |- ( E. x e. A E. y e. B ph -> ps )

  proof
    wph
    vy
    cB
    wrex
    wps
    vx
    cA
    vx
    cv
    cA
    wcel
    wph
    wps
    vy
    cB
    rexlimivv.1
    rexlimdva
    rexlimiv
end
