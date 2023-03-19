include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cvv.mm"
include "elex.mm"
include "cv.mm"
include "wi.mm"
include "nfel1.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "nfeq.mm"
include "nfim.mm"
include "eleq1d.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "fvmpt2.mm"
include "ex.mm"
include "vtoclgaf.mm"
include "syl5.mm"
include "imp.mm"

theorem fvmptf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cV: class V
  assume fvmptf.1: |- F/_ x A
  assume fvmptf.2: |- F/_ x C
  assume fvmptf.3: |- ( x = A -> B = C )
  assume fvmptf.4: |- F = ( x e. D |-> B )

  disjoint D x
  assert |- ( ( A e. D /\ C e. V ) -> ( F ` A ) = C )

  proof
    cA
    cD
    wcel
    #
    cC
    cV
    wcel
    #
    cA
    cF
    cfv
    #
    cC
    wceq
    #
    @1
    cC
    cvv
    wcel
    #
    @0
    @3
    cC
    cV
    elex
    cB
    cvv
    wcel
    #
    vx
    cv
    #
    cF
    cfv
    #
    cB
    wceq
    #
    wi
    @4
    @3
    wi
    vx
    cA
    cD
    fvmptf.1
    @4
    @3
    vx
    vx
    cC
    cvv
    fvmptf.2
    nfel1
    vx
    @2
    cC
    vx
    cA
    cF
    vx
    cF
    vx
    cD
    cB
    cmpt
    fvmptf.4
    vx
    cD
    cB
    nfmpt1
    nfcxfr
    fvmptf.1
    nffv
    fvmptf.2
    nfeq
    nfim
    @6
    cA
    wceq
    #
    @5
    @4
    @8
    @3
    @9
    cB
    cC
    cvv
    fvmptf.3
    eleq1d
    @9
    @7
    @2
    cB
    cC
    @6
    cA
    cF
    fveq2
    fvmptf.3
    eqeq12d
    imbi12d
    @6
    cD
    wcel
    @5
    @8
    vx
    cD
    cB
    cvv
    cF
    fvmptf.4
    fvmpt2
    ex
    vtoclgaf
    syl5
    imp
end
