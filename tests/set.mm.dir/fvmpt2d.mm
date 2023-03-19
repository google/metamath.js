include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cmpt.mm"
include "wceq.mm"
include "fveq1d.mm"
include "adantr.mm"
include "id.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2an2.mm"
include "eqtrd.mm"

theorem fvmpt2d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  assume fvmpt2d.1: |- ( ph -> F = ( x e. A |-> B ) )
  assume fvmpt2d.4: |- ( ( ph /\ x e. A ) -> B e. V )

  disjoint A x
  assert |- ( ( ph /\ x e. A ) -> ( F ` x ) = B )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wa
    @0
    cF
    cfv
    #
    @0
    vx
    cA
    cB
    cmpt
    #
    cfv
    #
    cB
    wph
    @2
    @4
    wceq
    @1
    wph
    @0
    cF
    @3
    fvmpt2d.1
    fveq1d
    adantr
    @1
    @1
    wph
    cB
    cV
    wcel
    @4
    cB
    wceq
    @1
    id
    fvmpt2d.4
    vx
    cA
    cB
    cV
    @3
    @3
    eqid
    fvmpt2
    syl2an2
    eqtrd
end
