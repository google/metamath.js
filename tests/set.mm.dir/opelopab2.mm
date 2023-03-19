include "cv.mm"
include "wceq.mm"
include "sylan9bb.mm"
include "opelopab2a.mm"

theorem opelopab2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume opelopab2.1: |- ( x = A -> ( ph <-> ps ) )
  assume opelopab2.2: |- ( y = B -> ( ps <-> ch ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint ch x
  disjoint ch y
  assert |- ( ( A e. C /\ B e. D ) -> ( <. A , B >. e. { <. x , y >. | ( ( x e. C /\ y e. D ) /\ ph ) } <-> ch ) )

  proof
    wph
    wch
    vx
    vy
    cA
    cB
    cC
    cD
    vx
    cv
    cA
    wceq
    wph
    wps
    vy
    cv
    cB
    wceq
    wch
    opelopab2.1
    opelopab2.2
    sylan9bb
    opelopab2a
end
