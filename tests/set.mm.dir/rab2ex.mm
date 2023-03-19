include "rabex2.mm"
include "rabex.mm"

theorem rab2ex
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume rab2ex.1: |- B = { y e. A | ps }
  assume rab2ex.2: |- A e. _V

  disjoint B x
  disjoint A y
  assert |- { x e. B | ph } e. _V

  proof
    wph
    vx
    cB
    wps
    vy
    cA
    cB
    rab2ex.1
    rab2ex.2
    rabex2
    rabex
end
