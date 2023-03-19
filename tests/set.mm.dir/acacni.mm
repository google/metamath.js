include "wac.mm"
include "wcel.mm"
include "wa.mm"
include "wacn.mm"
include "cvv.mm"
include "cv.mm"
include "ccrd.mm"
include "cdm.mm"
include "simpr.mm"
include "vex.mm"
include "wceq.mm"
include "simpl.mm"
include "dfac10.mm"
include "sylib.mm"
include "syl5eleqr.mm"
include "numacn.mm"
include "sylc.mm"
include "a1i.mm"
include "2thd.mm"
include "eqrdv.mm"

theorem acacni
  let cA: class A
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( CHOICE /\ A e. V ) -> AC_ A = _V )

  proof
    wac
    cA
    cV
    wcel
    #
    wa
    #
    vx
    cA
    wacn
    #
    cvv
    @1
    vx
    cv
    #
    @2
    wcel
    #
    @3
    cvv
    wcel
    #
    @1
    @0
    @3
    ccrd
    cdm
    #
    wcel
    @4
    wac
    @0
    simpr
    @1
    @3
    cvv
    @6
    vx
    vex
    #
    @1
    wac
    @6
    cvv
    wceq
    wac
    @0
    simpl
    dfac10
    sylib
    syl5eleqr
    cA
    cV
    @3
    numacn
    sylc
    @5
    @1
    @7
    a1i
    2thd
    eqrdv
end
