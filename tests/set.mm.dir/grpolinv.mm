include "cgr.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "grpoinv.mm"
include "simpld.mm"

theorem grpolinv
  let cA: class A
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  let vy: setvar y
  assume grpinv.1: |- X = ran G
  assume grpinv.2: |- U = ( GId ` G )
  assume grpinv.3: |- N = ( inv ` G )


  assert |- ( ( G e. GrpOp /\ A e. X ) -> ( ( N ` A ) G A ) = U )

  proof
    cG
    cgr
    wcel
    cA
    cX
    wcel
    wa
    cA
    cN
    cfv
    #
    cA
    cG
    co
    cU
    wceq
    cA
    @0
    cG
    co
    cU
    wceq
    cA
    cU
    cG
    cN
    cX
    grpinv.1
    grpinv.2
    grpinv.3
    grpoinv
    simpld
end
