include "nfcv.mm"
include "nfv.mm"
include "vtocl2gaf.mm"

theorem vtocl2ga
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume vtocl2ga.1: |- ( x = A -> ( ph <-> ps ) )
  assume vtocl2ga.2: |- ( y = B -> ( ps <-> ch ) )
  assume vtocl2ga.3: |- ( ( x e. C /\ y e. D ) -> ph )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint ps x
  disjoint ch y
  assert |- ( ( A e. C /\ B e. D ) -> ch )

  proof
    wph
    wps
    wch
    vx
    vy
    cA
    cB
    cC
    cD
    vx
    cA
    nfcv
    vy
    cA
    nfcv
    vy
    cB
    nfcv
    wps
    vx
    nfv
    wch
    vy
    nfv
    vtocl2ga.1
    vtocl2ga.2
    vtocl2ga.3
    vtocl2gaf
end
