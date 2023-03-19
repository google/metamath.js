include "nfv.mm"
include "rspc2.mm"

theorem rspc2v
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume rspc2v.1: |- ( x = A -> ( ph <-> ch ) )
  assume rspc2v.2: |- ( y = B -> ( ch <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint C x
  disjoint D x
  disjoint D y
  disjoint ch x
  disjoint ps y
  assert |- ( ( A e. C /\ B e. D ) -> ( A. x e. C A. y e. D ph -> ps ) )

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
    wch
    vx
    nfv
    wps
    vy
    nfv
    rspc2v.1
    rspc2v.2
    rspc2
end
