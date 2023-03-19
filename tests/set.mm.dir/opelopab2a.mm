include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cv.mm"
include "copab.mm"
include "wceq.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "anbi12d.mm"
include "opelopabga.mm"
include "bianabs.mm"

theorem opelopab2a
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume opelopabga.1: |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ps x
  disjoint ps y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  assert |- ( ( A e. C /\ B e. D ) -> ( <. A , B >. e. { <. x , y >. | ( ( x e. C /\ y e. D ) /\ ph ) } <-> ps ) )

  proof
    cA
    cC
    wcel
    #
    cB
    cD
    wcel
    #
    wa
    #
    cA
    cB
    cop
    vx
    cv
    #
    cC
    wcel
    #
    vy
    cv
    #
    cD
    wcel
    #
    wa
    #
    wph
    wa
    #
    vx
    vy
    copab
    wcel
    wps
    @8
    @2
    wps
    wa
    vx
    vy
    cA
    cB
    cC
    cD
    @3
    cA
    wceq
    #
    @5
    cB
    wceq
    #
    wa
    @7
    @2
    wph
    wps
    @9
    @4
    @0
    @10
    @6
    @1
    @3
    cA
    cC
    eleq1
    @5
    cB
    cD
    eleq1
    bi2anan9
    opelopabga.1
    anbi12d
    opelopabga
    bianabs
end
