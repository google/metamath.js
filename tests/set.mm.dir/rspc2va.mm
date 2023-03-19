include "wcel.mm"
include "wa.mm"
include "wral.mm"
include "rspc2v.mm"
include "imp.mm"

theorem rspc2va
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
  assert |- ( ( ( A e. C /\ B e. D ) /\ A. x e. C A. y e. D ph ) -> ps )

  proof
    cA
    cC
    wcel
    cB
    cD
    wcel
    wa
    wph
    vy
    cD
    wral
    vx
    cC
    wral
    wps
    wph
    wps
    wch
    vx
    vy
    cA
    cB
    cC
    cD
    rspc2v.1
    rspc2v.2
    rspc2v
    imp
end
