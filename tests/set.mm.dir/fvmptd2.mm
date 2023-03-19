include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "fvmptd.mm"

theorem fvmptd2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cV: class V
  assume fvmptd2.1: |- F = ( x e. D |-> B )
  assume fvmptd2.2: |- ( ( ph /\ x = A ) -> B = C )
  assume fvmptd2.3: |- ( ph -> A e. D )
  assume fvmptd2.4: |- ( ph -> C e. V )

  disjoint A x
  disjoint C x
  disjoint D x
  disjoint ph x
  assert |- ( ph -> ( F ` A ) = C )

  proof
    wph
    vx
    cA
    cB
    cC
    cD
    cF
    cV
    cF
    vx
    cD
    cB
    cmpt
    wceq
    wph
    fvmptd2.1
    a1i
    fvmptd2.2
    fvmptd2.3
    fvmptd2.4
    fvmptd
end
