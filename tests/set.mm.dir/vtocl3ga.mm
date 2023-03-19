include "nfcv.mm"
include "nfv.mm"
include "vtocl3gaf.mm"

theorem vtocl3ga
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  assume vtocl3ga.1: |- ( x = A -> ( ph <-> ps ) )
  assume vtocl3ga.2: |- ( y = B -> ( ps <-> ch ) )
  assume vtocl3ga.3: |- ( z = C -> ( ch <-> th ) )
  assume vtocl3ga.4: |- ( ( x e. D /\ y e. R /\ z e. S ) -> ph )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C z
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint ps x
  disjoint ch y
  disjoint th z
  assert |- ( ( A e. D /\ B e. R /\ C e. S ) -> th )

  proof
    wph
    wps
    wch
    wth
    vx
    vy
    vz
    cA
    cB
    cC
    cD
    cR
    cS
    vx
    cA
    nfcv
    vy
    cA
    nfcv
    vz
    cA
    nfcv
    vy
    cB
    nfcv
    vz
    cB
    nfcv
    vz
    cC
    nfcv
    wps
    vx
    nfv
    wch
    vy
    nfv
    wth
    vz
    nfv
    vtocl3ga.1
    vtocl3ga.2
    vtocl3ga.3
    vtocl3ga.4
    vtocl3gaf
end
