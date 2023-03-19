include "wcel.mm"
include "cr.mm"
include "ctimesr.mm"
include "co.mm"
include "cfv.mm"
include "cmul.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cmpt.mm"
include "mulvval.mm"
include "fveq1d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"
include "3impa.mm"

theorem mulvfv
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let vx: setvar x


  assert |- ( ( A e. E /\ B e. D /\ C e. RR ) -> ( ( A .v B ) ` C ) = ( A x. ( B ` C ) ) )

  proof
    cA
    cE
    wcel
    #
    cB
    cD
    wcel
    #
    cC
    cr
    wcel
    #
    cC
    cA
    cB
    ctimesr
    co
    #
    cfv
    #
    cA
    cC
    cB
    cfv
    #
    cmul
    co
    #
    wceq
    @0
    @1
    wa
    #
    @2
    @4
    cC
    vx
    cr
    cA
    vx
    cv
    #
    cB
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    cfv
    @6
    @7
    cC
    @3
    @11
    vx
    cA
    cB
    cE
    cD
    mulvval
    fveq1d
    vx
    cC
    @10
    @6
    cr
    @11
    @8
    cC
    wceq
    @9
    @5
    cA
    cmul
    @8
    cC
    cB
    fveq2
    oveq2d
    @11
    eqid
    cA
    @5
    cmul
    ovex
    fvmpt
    sylan9eq
    3impa
end
