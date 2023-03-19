include "cgr.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "co.mm"
include "wa.mm"
include "oveq2.mm"
include "adantl.mm"
include "grporinv.mm"
include "3adant3.mm"
include "adantr.mm"
include "eqtr3d.mm"
include "grpolinv.mm"
include "oveq1d.mm"
include "grpoinvcl.mm"
include "adantrr.mm"
include "simprl.mm"
include "simprr.mm"
include "3jca.mm"
include "grpoass.mm"
include "syldan.mm"
include "3impb.mm"
include "grpolid.mm"
include "3adant2.mm"
include "grporid.mm"
include "3eqtr3rd.mm"
include "impbida.mm"

theorem grpoinvid1
  let cA: class A
  let cB: class B
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  let vy: setvar y
  assume grpinv.1: |- X = ran G
  assume grpinv.2: |- U = ( GId ` G )
  assume grpinv.3: |- N = ( inv ` G )


  assert |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) -> ( ( N ` A ) = B <-> ( A G B ) = U ) )

  proof
    cG
    cgr
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    cN
    cfv
    #
    cB
    wceq
    #
    cA
    cB
    cG
    co
    #
    cU
    wceq
    #
    @3
    @5
    wa
    cA
    @4
    cG
    co
    #
    @6
    cU
    @5
    @8
    @6
    wceq
    @3
    @4
    cB
    cA
    cG
    oveq2
    adantl
    @3
    @8
    cU
    wceq
    #
    @5
    @0
    @1
    @9
    @2
    cA
    cU
    cG
    cN
    cX
    grpinv.1
    grpinv.2
    grpinv.3
    grporinv
    3adant3
    adantr
    eqtr3d
    @3
    @7
    wa
    @4
    @6
    cG
    co
    #
    @4
    cU
    cG
    co
    #
    cB
    @4
    @7
    @10
    @11
    wceq
    @3
    @6
    cU
    @4
    cG
    oveq2
    adantl
    @3
    @10
    cB
    wceq
    @7
    @3
    cU
    cB
    cG
    co
    #
    @10
    cB
    @3
    @4
    cA
    cG
    co
    #
    cB
    cG
    co
    #
    @12
    @10
    @0
    @1
    @14
    @12
    wceq
    @2
    @0
    @1
    wa
    @13
    cU
    cB
    cG
    cA
    cU
    cG
    cN
    cX
    grpinv.1
    grpinv.2
    grpinv.3
    grpolinv
    oveq1d
    3adant3
    @0
    @1
    @2
    @14
    @10
    wceq
    #
    @0
    @1
    @2
    wa
    #
    @4
    cX
    wcel
    #
    @1
    @2
    w3a
    @15
    @0
    @16
    wa
    @17
    @1
    @2
    @0
    @1
    @17
    @2
    cA
    cG
    cN
    cX
    grpinv.1
    grpinv.3
    grpoinvcl
    #
    adantrr
    @0
    @1
    @2
    simprl
    @0
    @1
    @2
    simprr
    3jca
    @4
    cA
    cB
    cG
    cX
    grpinv.1
    grpoass
    syldan
    3impb
    eqtr3d
    @0
    @2
    @12
    cB
    wceq
    @1
    cB
    cU
    cG
    cX
    grpinv.1
    grpinv.2
    grpolid
    3adant2
    eqtr3d
    adantr
    @3
    @11
    @4
    wceq
    #
    @7
    @0
    @1
    @19
    @2
    @0
    @1
    @17
    @19
    @18
    @4
    cU
    cG
    cX
    grpinv.1
    grpinv.2
    grporid
    syldan
    3adant3
    adantr
    3eqtr3rd
    impbida
end
