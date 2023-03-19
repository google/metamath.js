include "wcel.mm"
include "wa.mm"
include "ctimesr.mm"
include "co.mm"
include "cr.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "cmpt.mm"
include "ovex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "mulvval.mm"
include "fneq1d.mm"
include "mpbiri.mm"

theorem mulvfn
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x


  assert |- ( ( A e. C /\ B e. D ) -> ( A .v B ) Fn RR )

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
    ctimesr
    co
    #
    cr
    wfn
    vx
    cr
    cA
    vx
    cv
    cB
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    cr
    wfn
    vx
    cr
    @3
    @4
    cA
    @2
    cmul
    ovex
    @4
    eqid
    fnmpti
    @0
    cr
    @1
    @4
    vx
    cA
    cB
    cC
    cD
    mulvval
    fneq1d
    mpbiri
end
