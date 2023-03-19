include "cgr.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "cgn.mm"
include "cfv.mm"
include "oveq2.mm"
include "adantl.mm"
include "cgi.mm"
include "eqid.mm"
include "grpolinv.mm"
include "adantlr.mm"
include "oveq1d.mm"
include "grpoinvcl.mm"
include "adantrl.mm"
include "simprr.mm"
include "simprl.mm"
include "3jca.mm"
include "grpoass.mm"
include "syldan.mm"
include "anassrs.mm"
include "grpolid.mm"
include "adantr.mm"
include "3eqtr3d.mm"
include "adantrr.mm"
include "exp53.mm"
include "3imp2.mm"
include "impbid1.mm"

theorem grpolcan
  let cA: class A
  let cB: class B
  let cC: class C
  let cG: class G
  let cX: class X
  assume grplcan.1: |- X = ran G


  assert |- ( ( G e. GrpOp /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( C G A ) = ( C G B ) <-> A = B ) )

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
    cC
    cX
    wcel
    #
    w3a
    wa
    cC
    cA
    cG
    co
    #
    cC
    cB
    cG
    co
    #
    wceq
    #
    cA
    cB
    wceq
    #
    @0
    @1
    @2
    @3
    @6
    @7
    wi
    @0
    @1
    @2
    @3
    @6
    @7
    @0
    @1
    wa
    #
    @2
    @3
    wa
    #
    wa
    #
    @6
    wa
    cC
    cG
    cgn
    cfv
    #
    cfv
    #
    @4
    cG
    co
    #
    @12
    @5
    cG
    co
    #
    cA
    cB
    @6
    @13
    @14
    wceq
    @10
    @4
    @5
    @12
    cG
    oveq2
    adantl
    @10
    @13
    cA
    wceq
    #
    @6
    @8
    @3
    @15
    @2
    @8
    @3
    wa
    #
    @12
    cC
    cG
    co
    #
    cA
    cG
    co
    #
    cG
    cgi
    cfv
    #
    cA
    cG
    co
    #
    @13
    cA
    @16
    @17
    @19
    cA
    cG
    @0
    @3
    @17
    @19
    wceq
    #
    @1
    cC
    @19
    cG
    @11
    cX
    grplcan.1
    @19
    eqid
    #
    @11
    eqid
    #
    grpolinv
    #
    adantlr
    oveq1d
    @0
    @1
    @3
    @18
    @13
    wceq
    #
    @0
    @1
    @3
    wa
    #
    @12
    cX
    wcel
    #
    @3
    @1
    w3a
    @25
    @0
    @26
    wa
    @27
    @3
    @1
    @0
    @3
    @27
    @1
    cC
    cG
    @11
    cX
    grplcan.1
    @23
    grpoinvcl
    #
    adantrl
    @0
    @1
    @3
    simprr
    @0
    @1
    @3
    simprl
    3jca
    @12
    cC
    cA
    cG
    cX
    grplcan.1
    grpoass
    syldan
    anassrs
    @8
    @20
    cA
    wceq
    @3
    cA
    @19
    cG
    cX
    grplcan.1
    @22
    grpolid
    adantr
    3eqtr3d
    adantrl
    adantr
    @10
    @14
    cB
    wceq
    #
    @6
    @0
    @9
    @29
    @1
    @0
    @9
    wa
    #
    @17
    cB
    cG
    co
    #
    @19
    cB
    cG
    co
    #
    @14
    cB
    @30
    @17
    @19
    cB
    cG
    @0
    @3
    @21
    @2
    @24
    adantrl
    oveq1d
    @0
    @9
    @27
    @3
    @2
    w3a
    @31
    @14
    wceq
    @30
    @27
    @3
    @2
    @0
    @3
    @27
    @2
    @28
    adantrl
    @0
    @2
    @3
    simprr
    @0
    @2
    @3
    simprl
    3jca
    @12
    cC
    cB
    cG
    cX
    grplcan.1
    grpoass
    syldan
    @0
    @2
    @32
    cB
    wceq
    @3
    cB
    @19
    cG
    cX
    grplcan.1
    @22
    grpolid
    adantrr
    3eqtr3d
    adantlr
    adantr
    3eqtr3d
    exp53
    3imp2
    cA
    cB
    cC
    cG
    oveq2
    impbid1
end
