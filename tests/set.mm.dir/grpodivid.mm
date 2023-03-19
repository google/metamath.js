include "cgr.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cgn.mm"
include "cfv.mm"
include "wceq.mm"
include "eqid.mm"
include "grpodivval.mm"
include "3anidm23.mm"
include "grporinv.mm"
include "eqtrd.mm"

theorem grpodivid
  let cA: class A
  let cD: class D
  let cU: class U
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume grpdivf.1: |- X = ran G
  assume grpdivf.3: |- D = ( /g ` G )
  assume grpdivid.3: |- U = ( GId ` G )


  assert |- ( ( G e. GrpOp /\ A e. X ) -> ( A D A ) = U )

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
    cA
    cA
    cD
    co
    #
    cA
    cA
    cG
    cgn
    cfv
    #
    cfv
    cG
    co
    #
    cU
    @0
    @1
    @2
    @4
    wceq
    cA
    cA
    cD
    cG
    @3
    cX
    grpdivf.1
    @3
    eqid
    #
    grpdivf.3
    grpodivval
    3anidm23
    cA
    cU
    cG
    @3
    cX
    grpdivf.1
    grpdivid.3
    @5
    grporinv
    eqtrd
end
