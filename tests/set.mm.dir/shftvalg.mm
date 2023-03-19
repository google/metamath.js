include "wcel.mm"
include "cc.mm"
include "cshi.mm"
include "co.mm"
include "cfv.mm"
include "cmin.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "oveq1.mm"
include "fveq1d.mm"
include "fveq1.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "vex.mm"
include "shftval.mm"
include "vtoclg.mm"
include "3impib.mm"

theorem shftvalg
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let vf: setvar f


  assert |- ( ( F e. V /\ A e. CC /\ B e. CC ) -> ( ( F shift A ) ` B ) = ( F ` ( B - A ) ) )

  proof
    cF
    cV
    wcel
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cB
    cF
    cA
    cshi
    co
    #
    cfv
    #
    cB
    cA
    cmin
    co
    #
    cF
    cfv
    #
    wceq
    #
    @0
    @1
    wa
    #
    cB
    vf
    cv
    #
    cA
    cshi
    co
    #
    cfv
    #
    @4
    @8
    cfv
    #
    wceq
    #
    wi
    @7
    @6
    wi
    vf
    cF
    cV
    @8
    cF
    wceq
    #
    @12
    @6
    @7
    @13
    @10
    @3
    @11
    @5
    @13
    cB
    @9
    @2
    @8
    cF
    cA
    cshi
    oveq1
    fveq1d
    @4
    @8
    cF
    fveq1
    eqeq12d
    imbi2d
    cA
    cB
    @8
    vf
    vex
    shftval
    vtoclg
    3impib
end
