include "cgr.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cgi.mm"
include "grpoinvcl.mm"
include "eqid.mm"
include "grporinv.mm"
include "syldan.mm"
include "grpolinv.mm"
include "eqtr4d.mm"
include "w3a.mm"
include "wb.mm"
include "simpr.mm"
include "3jca.mm"
include "grpolcan.mm"
include "mpbid.mm"

theorem grpo2inv
  let cA: class A
  let cG: class G
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume grpasscan1.1: |- X = ran G
  assume grpasscan1.2: |- N = ( inv ` G )


  assert |- ( ( G e. GrpOp /\ A e. X ) -> ( N ` ( N ` A ) ) = A )

  proof
    cG
    cgr
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cA
    cN
    cfv
    #
    @3
    cN
    cfv
    #
    cG
    co
    #
    @3
    cA
    cG
    co
    #
    wceq
    #
    @4
    cA
    wceq
    #
    @2
    @5
    cG
    cgi
    cfv
    #
    @6
    @0
    @1
    @3
    cX
    wcel
    #
    @5
    @9
    wceq
    cA
    cG
    cN
    cX
    grpasscan1.1
    grpasscan1.2
    grpoinvcl
    #
    @3
    @9
    cG
    cN
    cX
    grpasscan1.1
    @9
    eqid
    #
    grpasscan1.2
    grporinv
    syldan
    cA
    @9
    cG
    cN
    cX
    grpasscan1.1
    @12
    grpasscan1.2
    grpolinv
    eqtr4d
    @0
    @1
    @4
    cX
    wcel
    #
    @1
    @10
    w3a
    @7
    @8
    wb
    @2
    @13
    @1
    @10
    @0
    @1
    @10
    @13
    @11
    @3
    cG
    cN
    cX
    grpasscan1.1
    grpasscan1.2
    grpoinvcl
    syldan
    @0
    @1
    simpr
    @11
    3jca
    @4
    cA
    @3
    cG
    cX
    grpasscan1.1
    grpolcan
    syldan
    mpbid
end
