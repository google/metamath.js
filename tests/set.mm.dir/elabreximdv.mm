include "nfv.mm"
include "elabreximd.mm"

theorem elabreximdv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  assume elabreximdv.1: |- ( A = B -> ( ch <-> ps ) )
  assume elabreximdv.2: |- ( ph -> A e. V )
  assume elabreximdv.3: |- ( ( ph /\ x e. C ) -> ps )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint ch x
  disjoint ph x
  assert |- ( ( ph /\ A e. { y | E. x e. C y = B } ) -> ch )

  proof
    wph
    wps
    wch
    vx
    vy
    cA
    cB
    cC
    cV
    wph
    vx
    nfv
    wch
    vx
    nfv
    elabreximdv.1
    elabreximdv.2
    elabreximdv.3
    elabreximd
end
