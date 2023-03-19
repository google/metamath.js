include "cgr.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "id.mm"
include "3anidm23.mm"
include "grpoass.mm"
include "sylan2.mm"
include "adantr.mm"
include "oveq1.mm"
include "ad2antrl.mm"
include "oveq2.mm"
include "ad2antll.mm"
include "simprl.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"

theorem grpoidinvlem1
  let cA: class A
  let cU: class U
  let cG: class G
  let cX: class X
  let cY: class Y
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let vu: setvar u
  assume grpfo.1: |- X = ran G


  assert |- ( ( ( G e. GrpOp /\ ( Y e. X /\ A e. X ) ) /\ ( ( Y G A ) = U /\ ( A G A ) = A ) ) -> ( U G A ) = U )

  proof
    cG
    cgr
    wcel
    #
    cY
    cX
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    wa
    #
    cY
    cA
    cG
    co
    #
    cU
    wceq
    #
    cA
    cA
    cG
    co
    #
    cA
    wceq
    #
    wa
    #
    wa
    #
    @5
    cA
    cG
    co
    #
    cY
    @7
    cG
    co
    #
    cU
    cA
    cG
    co
    #
    cU
    @4
    @11
    @12
    wceq
    #
    @9
    @3
    @0
    @1
    @2
    @2
    w3a
    #
    @14
    @1
    @2
    @15
    @15
    id
    3anidm23
    cY
    cA
    cA
    cG
    cX
    grpfo.1
    grpoass
    sylan2
    adantr
    @6
    @11
    @13
    wceq
    @4
    @8
    @5
    cU
    cA
    cG
    oveq1
    ad2antrl
    @10
    @12
    @5
    cU
    @8
    @12
    @5
    wceq
    @4
    @6
    @7
    cA
    cY
    cG
    oveq2
    ad2antll
    @4
    @6
    @8
    simprl
    eqtrd
    3eqtr3d
end
