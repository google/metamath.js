include "cgr.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "co.mm"
include "wa.mm"
include "oveq1.mm"
include "adantl.mm"
include "grpolinv.mm"
include "3adant3.mm"
include "adantr.mm"
include "eqtr3d.mm"
include "grpoinvcl.mm"
include "grpolid.mm"
include "syldan.mm"
include "eqcomd.mm"
include "simprr.mm"
include "simprl.mm"
include "adantrr.mm"
include "3jca.mm"
include "grpoass.mm"
include "3impb.mm"
include "grporinv.mm"
include "oveq2d.mm"
include "grporid.mm"
include "3adant2.mm"
include "3eqtrd.mm"
include "3eqtr2d.mm"
include "impbida.mm"

theorem grpoinvid2
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


  assert |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) -> ( ( N ` A ) = B <-> ( B G A ) = U ) )

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
    cB
    cA
    cG
    co
    #
    cU
    wceq
    #
    @3
    @5
    wa
    @4
    cA
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
    oveq1
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
    grpolinv
    3adant3
    adantr
    eqtr3d
    @3
    @7
    wa
    @4
    cU
    @4
    cG
    co
    #
    @6
    @4
    cG
    co
    #
    cB
    @3
    @4
    @10
    wceq
    @7
    @3
    @10
    @4
    @0
    @1
    @10
    @4
    wceq
    #
    @2
    @0
    @1
    @4
    cX
    wcel
    #
    @12
    cA
    cG
    cN
    cX
    grpinv.1
    grpinv.3
    grpoinvcl
    #
    @4
    cU
    cG
    cX
    grpinv.1
    grpinv.2
    grpolid
    syldan
    3adant3
    eqcomd
    adantr
    @7
    @11
    @10
    wceq
    @3
    @6
    cU
    @4
    cG
    oveq1
    adantl
    @3
    @11
    cB
    wceq
    @7
    @3
    @11
    cB
    cA
    @4
    cG
    co
    #
    cG
    co
    #
    cB
    cU
    cG
    co
    #
    cB
    @0
    @1
    @2
    @11
    @16
    wceq
    #
    @0
    @1
    @2
    wa
    #
    @2
    @1
    @13
    w3a
    @18
    @0
    @19
    wa
    @2
    @1
    @13
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
    @13
    @2
    @14
    adantrr
    3jca
    cB
    cA
    @4
    cG
    cX
    grpinv.1
    grpoass
    syldan
    3impb
    @0
    @1
    @16
    @17
    wceq
    @2
    @0
    @1
    wa
    @15
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
    grporinv
    oveq2d
    3adant3
    @0
    @2
    @17
    cB
    wceq
    @1
    cB
    cU
    cG
    cX
    grpinv.1
    grpinv.2
    grporid
    3adant2
    3eqtrd
    adantr
    3eqtr2d
    impbida
end
