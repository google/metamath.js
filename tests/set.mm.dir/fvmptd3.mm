include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "nfcv.mm"
include "fvmptf.mm"
include "syl2anc.mm"

theorem fvmptd3
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cV: class V
  assume fvmptd3.1: |- F = ( x e. D |-> B )
  assume fvmptd3.2: |- ( x = A -> B = C )
  assume fvmptd3.3: |- ( ph -> A e. D )
  assume fvmptd3.4: |- ( ph -> C e. V )

  disjoint A x
  disjoint C x
  disjoint D x
  assert |- ( ph -> ( F ` A ) = C )

  proof
    wph
    cA
    cD
    wcel
    cC
    cV
    wcel
    cA
    cF
    cfv
    cC
    wceq
    fvmptd3.3
    fvmptd3.4
    vx
    cA
    cB
    cC
    cD
    cF
    cV
    vx
    cA
    nfcv
    vx
    cC
    nfcv
    fvmptd3.2
    fvmptd3.1
    fvmptf
    syl2anc
end
