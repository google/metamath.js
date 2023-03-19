include "nfv.mm"
include "fvmptd3f.mm"

theorem fvmptdf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cF: class F
  let cV: class V
  assume fvmptdf.1: |- ( ph -> A e. D )
  assume fvmptdf.2: |- ( ( ph /\ x = A ) -> B e. V )
  assume fvmptdf.3: |- ( ( ph /\ x = A ) -> ( ( F ` A ) = B -> ps ) )
  assume fvmptdf.4: |- F/_ x F
  assume fvmptdf.5: |- F/ x ps

  disjoint A x
  disjoint D x
  disjoint ph x
  assert |- ( ph -> ( F = ( x e. D |-> B ) -> ps ) )

  proof
    wph
    wps
    vx
    cA
    cB
    cD
    cF
    cV
    fvmptdf.1
    fvmptdf.2
    fvmptdf.3
    fvmptdf.4
    fvmptdf.5
    wph
    vx
    nfv
    fvmptd3f
end
