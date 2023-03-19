include "cfv.mm"
include "cmpt.mm"
include "csb.mm"
include "fveq1d.mm"
include "wcel.mm"
include "wceq.mm"
include "csbied.mm"
include "eqeltrd.mm"
include "eqid.mm"
include "fvmpts.mm"
include "syl2anc.mm"
include "3eqtrd.mm"

theorem fvmptd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cV: class V
  assume fvmptd.1: |- ( ph -> F = ( x e. D |-> B ) )
  assume fvmptd.2: |- ( ( ph /\ x = A ) -> B = C )
  assume fvmptd.3: |- ( ph -> A e. D )
  assume fvmptd.4: |- ( ph -> C e. V )

  disjoint A x
  disjoint C x
  disjoint D x
  disjoint ph x
  assert |- ( ph -> ( F ` A ) = C )

  proof
    wph
    cA
    cF
    cfv
    cA
    vx
    cD
    cB
    cmpt
    #
    cfv
    #
    vx
    cA
    cB
    csb
    #
    cC
    wph
    cA
    cF
    @0
    fvmptd.1
    fveq1d
    wph
    cA
    cD
    wcel
    @2
    cV
    wcel
    @1
    @2
    wceq
    fvmptd.3
    wph
    @2
    cC
    cV
    wph
    vx
    cA
    cB
    cC
    cD
    fvmptd.3
    fvmptd.2
    csbied
    #
    fvmptd.4
    eqeltrd
    vx
    cA
    cB
    cD
    @0
    cV
    @0
    eqid
    fvmpts
    syl2anc
    @3
    3eqtrd
end
