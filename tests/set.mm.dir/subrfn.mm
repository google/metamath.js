include "wcel.mm"
include "wa.mm"
include "cminusr.mm"
include "co.mm"
include "cr.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "cmpt.mm"
include "ovex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "subrval.mm"
include "fneq1d.mm"
include "mpbiri.mm"

theorem subrfn
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x


  assert |- ( ( A e. C /\ B e. D ) -> ( A -r B ) Fn RR )

  proof
    cA
    cC
    wcel
    cB
    cD
    wcel
    wa
    #
    cA
    cB
    cminusr
    co
    #
    cr
    wfn
    vx
    cr
    vx
    cv
    #
    cA
    cfv
    #
    @2
    cB
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    cr
    wfn
    vx
    cr
    @5
    @6
    @3
    @4
    cmin
    ovex
    @6
    eqid
    fnmpti
    @0
    cr
    @1
    @6
    vx
    cA
    cB
    cC
    cD
    subrval
    fneq1d
    mpbiri
end
