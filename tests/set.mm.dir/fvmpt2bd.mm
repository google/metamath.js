include "cv.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "cmpt.mm"
include "wceq.mm"
include "fveq1d.mm"
include "3ad2ant1.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "3adant1.mm"
include "eqtrd.mm"

theorem fvmpt2bd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume fvmpt2bd.1: |- ( ph -> F = ( x e. A |-> B ) )

  disjoint A x
  assert |- ( ( ph /\ x e. A /\ B e. C ) -> ( F ` x ) = B )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    #
    cB
    cC
    wcel
    #
    w3a
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
    @1
    @3
    @5
    wceq
    @2
    wph
    @0
    cF
    @4
    fvmpt2bd.1
    fveq1d
    3ad2ant1
    @1
    @2
    @5
    cB
    wceq
    wph
    vx
    cA
    cB
    cC
    @4
    @4
    eqid
    fvmpt2
    3adant1
    eqtrd
end
