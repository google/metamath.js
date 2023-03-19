include "cgr.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "simprr.mm"
include "simprl.mm"
include "grpocl.mm"
include "3com23.mm"
include "3expb.mm"
include "3jca.mm"
include "grpoass.mm"
include "syldan.mm"
include "adantr.mm"
include "oveq1.mm"
include "adantl.mm"
include "simpl.mm"
include "eqtr2d.mm"
include "id.mm"
include "3anidm13.mm"
include "sylan2.mm"
include "sylan9eqr.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem grpoidinvlem2
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


  assert |- ( ( ( G e. GrpOp /\ ( Y e. X /\ A e. X ) ) /\ ( ( U G Y ) = Y /\ ( Y G A ) = U ) ) -> ( ( A G Y ) G ( A G Y ) ) = ( A G Y ) )

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
    cU
    cY
    cG
    co
    #
    cY
    wceq
    #
    cY
    cA
    cG
    co
    #
    cU
    wceq
    #
    wa
    #
    wa
    #
    cA
    cY
    cG
    co
    #
    @11
    cG
    co
    #
    cA
    cY
    @11
    cG
    co
    #
    cG
    co
    #
    @11
    @4
    @12
    @14
    wceq
    #
    @9
    @0
    @3
    @2
    @1
    @11
    cX
    wcel
    #
    w3a
    @15
    @4
    @2
    @1
    @16
    @0
    @1
    @2
    simprr
    @0
    @1
    @2
    simprl
    @0
    @1
    @2
    @16
    @0
    @2
    @1
    @16
    cA
    cY
    cG
    cX
    grpfo.1
    grpocl
    3com23
    3expb
    3jca
    cA
    cY
    @11
    cG
    cX
    grpfo.1
    grpoass
    syldan
    adantr
    @10
    @13
    cY
    cA
    cG
    @10
    cY
    @13
    @9
    @4
    cY
    @7
    cY
    cG
    co
    #
    @13
    @9
    @17
    @5
    cY
    @8
    @17
    @5
    wceq
    @6
    @7
    cU
    cY
    cG
    oveq1
    adantl
    @6
    @8
    simpl
    eqtr2d
    @3
    @0
    @1
    @2
    @1
    w3a
    #
    @17
    @13
    wceq
    @1
    @2
    @18
    @18
    id
    3anidm13
    cY
    cA
    cY
    cG
    cX
    grpfo.1
    grpoass
    sylan2
    sylan9eqr
    eqcomd
    oveq2d
    eqtrd
end
