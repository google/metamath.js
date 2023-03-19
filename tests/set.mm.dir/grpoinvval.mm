include "cgr.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "crio.mm"
include "cmpt.mm"
include "grpoinvfval.mm"
include "fveq1d.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "riotabidv.mm"
include "eqid.mm"
include "riotaex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem grpoinvval
  let vy: setvar y
  let cA: class A
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vg: setvar g
  assume grpinvfval.1: |- X = ran G
  assume grpinvfval.2: |- U = ( GId ` G )
  assume grpinvfval.3: |- N = ( inv ` G )

  disjoint A y
  disjoint G y
  disjoint X y
  disjoint x y
  disjoint A x
  disjoint g x
  disjoint g y
  disjoint G g
  disjoint G x
  disjoint X g
  disjoint X x
  disjoint U g
  disjoint U x
  assert |- ( ( G e. GrpOp /\ A e. X ) -> ( N ` A ) = ( iota_ y e. X ( y G A ) = U ) )

  proof
    cG
    cgr
    wcel
    #
    cA
    cX
    wcel
    cA
    cN
    cfv
    cA
    vx
    cX
    vy
    cv
    #
    vx
    cv
    #
    cG
    co
    #
    cU
    wceq
    #
    vy
    cX
    crio
    #
    cmpt
    #
    cfv
    @1
    cA
    cG
    co
    #
    cU
    wceq
    #
    vy
    cX
    crio
    #
    @0
    cA
    cN
    @6
    vx
    vy
    cU
    cG
    cN
    cX
    grpinvfval.1
    grpinvfval.2
    grpinvfval.3
    grpoinvfval
    fveq1d
    vx
    cA
    @5
    @9
    cX
    @6
    @2
    cA
    wceq
    #
    @4
    @8
    vy
    cX
    @10
    @3
    @7
    cU
    @2
    cA
    @1
    cG
    oveq2
    eqeq1d
    riotabidv
    @6
    eqid
    @8
    vy
    cX
    riotaex
    fvmpt
    sylan9eq
end
