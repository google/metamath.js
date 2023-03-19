include "wcel.mm"
include "elrab2.mm"
include "biancom.mm"

theorem rabeqel
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume rabeqel.1: |- B = { x e. A | ph }
  assume rabeqel.2: |- ( x = C -> ( ph <-> ps ) )

  disjoint A x
  disjoint C x
  disjoint ps x
  assert |- ( C e. B <-> ( ps /\ C e. A ) )

  proof
    cC
    cB
    wcel
    wps
    cC
    cA
    wcel
    wph
    wps
    vx
    cC
    cA
    cB
    rabeqel.2
    rabeqel.1
    elrab2
    biancom
end
