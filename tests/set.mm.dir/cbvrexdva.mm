include "weq.mm"
include "wa.mm"
include "eqidd.mm"
include "cbvrexdva2.mm"

theorem cbvrexdva
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume cbvraldva.1: |- ( ( ph /\ x = y ) -> ( ps <-> ch ) )

  disjoint ps y
  disjoint ch x
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( E. x e. A ps <-> E. y e. A ch ) )

  proof
    wph
    wps
    wch
    vx
    vy
    cA
    cA
    cbvraldva.1
    wph
    vx
    vy
    weq
    wa
    cA
    eqidd
    cbvrexdva2
end
