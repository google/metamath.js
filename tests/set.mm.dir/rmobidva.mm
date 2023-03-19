include "nfv.mm"
include "rmobida.mm"

theorem rmobidva
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume rmobidva.1: |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) )

  disjoint ph x
  assert |- ( ph -> ( E* x e. A ps <-> E* x e. A ch ) )

  proof
    wph
    wps
    wch
    vx
    cA
    wph
    vx
    nfv
    rmobidva.1
    rmobida
end
