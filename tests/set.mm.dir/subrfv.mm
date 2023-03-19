include "wcel.mm"
include "cr.mm"
include "cminusr.mm"
include "co.mm"
include "cfv.mm"
include "cmin.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cmpt.mm"
include "subrval.mm"
include "fveq1d.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"
include "3impa.mm"

theorem subrfv
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let vx: setvar x


  assert |- ( ( A e. E /\ B e. D /\ C e. RR ) -> ( ( A -r B ) ` C ) = ( ( A ` C ) - ( B ` C ) ) )

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
    cminusr
    co
    #
    cfv
    #
    cC
    cA
    cfv
    #
    cC
    cB
    cfv
    #
    cmin
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
    vx
    cv
    #
    cA
    cfv
    #
    @9
    cB
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    cfv
    @7
    @8
    cC
    @3
    @13
    vx
    cA
    cB
    cE
    cD
    subrval
    fveq1d
    vx
    cC
    @12
    @7
    cr
    @13
    @9
    cC
    wceq
    @10
    @5
    @11
    @6
    cmin
    @9
    cC
    cA
    fveq2
    @9
    cC
    cB
    fveq2
    oveq12d
    @13
    eqid
    @5
    @6
    cmin
    ovex
    fvmpt
    sylan9eq
    3impa
end
