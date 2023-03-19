include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "eqidd.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptco.mm"

theorem cofmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let vy: setvar y
  assume cofmpt.1: |- ( ph -> F : C --> D )
  assume cofmpt.2: |- ( ( ph /\ x e. A ) -> B e. C )

  disjoint A x
  disjoint C x
  disjoint F x
  disjoint ph x
  disjoint B y
  disjoint x y
  disjoint C y
  disjoint F y
  assert |- ( ph -> ( F o. ( x e. A |-> B ) ) = ( x e. A |-> ( F ` B ) ) )

  proof
    wph
    vx
    vy
    cA
    cC
    cB
    vy
    cv
    #
    cF
    cfv
    cB
    cF
    cfv
    vx
    cA
    cB
    cmpt
    #
    cF
    cofmpt.2
    wph
    @1
    eqidd
    wph
    vy
    cC
    cD
    cF
    cofmpt.1
    feqmptd
    @0
    cB
    cF
    fveq2
    fmptco
end
