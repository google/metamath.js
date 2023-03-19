include "cfv.mm"
include "wceq.mm"
include "cmpt.mm"
include "cvv.mm"
include "eqidd.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "elex.mm"
include "syl.mm"
include "isset.mm"
include "sylib.mm"
include "wa.mm"
include "eqeltrrd.mm"
include "exlimddv.mm"
include "fvmptd.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"

theorem fvmptdv2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cV: class V
  assume fvmptdv2.1: |- ( ph -> A e. D )
  assume fvmptdv2.2: |- ( ( ph /\ x = A ) -> B e. V )
  assume fvmptdv2.3: |- ( ( ph /\ x = A ) -> B = C )

  disjoint A x
  disjoint C x
  disjoint D x
  disjoint ph x
  assert |- ( ph -> ( F = ( x e. D |-> B ) -> ( F ` A ) = C ) )

  proof
    wph
    cA
    cF
    cfv
    #
    cC
    wceq
    cF
    vx
    cD
    cB
    cmpt
    #
    wceq
    #
    cA
    @1
    cfv
    #
    cC
    wceq
    wph
    vx
    cA
    cB
    cC
    cD
    @1
    cvv
    wph
    @1
    eqidd
    fvmptdv2.3
    fvmptdv2.1
    wph
    vx
    cv
    cA
    wceq
    #
    cC
    cvv
    wcel
    vx
    wph
    cA
    cvv
    wcel
    #
    @4
    vx
    wex
    wph
    cA
    cD
    wcel
    @5
    fvmptdv2.1
    cA
    cD
    elex
    syl
    vx
    cA
    isset
    sylib
    wph
    @4
    wa
    #
    cB
    cC
    cvv
    fvmptdv2.3
    @6
    cB
    cV
    wcel
    cB
    cvv
    wcel
    fvmptdv2.2
    cB
    cV
    elex
    syl
    eqeltrrd
    exlimddv
    fvmptd
    @2
    @0
    @3
    cC
    cA
    cF
    @1
    fveq1
    eqeq1d
    syl5ibrcom
end
