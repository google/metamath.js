include "nfv.mm"
include "rexbida.mm"

theorem rexbidvaALT
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume rexbidva.1: |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) )

  disjoint ph x
  assert |- ( ph -> ( E. x e. A ps <-> E. x e. A ch ) )

  proof
    wph
    wps
    wch
    vx
    cA
    wph
    vx
    nfv
    rexbidva.1
    rexbida
end
