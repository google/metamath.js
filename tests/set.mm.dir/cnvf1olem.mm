include "wrel.mm"
include "wcel.mm"
include "csn.mm"
include "ccnv.mm"
include "cuni.mm"
include "wceq.mm"
include "wa.mm"
include "c2nd.mm"
include "cfv.mm"
include "c1st.mm"
include "cop.mm"
include "simprr.mm"
include "1st2nd.mm"
include "adantrr.mm"
include "sneqd.mm"
include "cnveqd.mm"
include "unieqd.mm"
include "eqtrd.mm"
include "opswap.mm"
include "syl6eq.mm"
include "simprl.mm"
include "eqeltrrd.mm"
include "fvex.mm"
include "opelcnv.mm"
include "sylibr.mm"
include "eqeltrd.mm"
include "eqcomi.mm"
include "3eqtr4a.mm"
include "jca.mm"

theorem cnvf1olem
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( Rel A /\ ( B e. A /\ C = U. `' { B } ) ) -> ( C e. `' A /\ B = U. `' { C } ) )

  proof
    cA
    wrel
    #
    cB
    cA
    wcel
    #
    cC
    cB
    csn
    #
    ccnv
    #
    cuni
    #
    wceq
    #
    wa
    wa
    #
    cC
    cA
    ccnv
    #
    wcel
    cB
    cC
    csn
    #
    ccnv
    #
    cuni
    #
    wceq
    @6
    cC
    cB
    c2nd
    cfv
    #
    cB
    c1st
    cfv
    #
    cop
    #
    @7
    @6
    cC
    @12
    @11
    cop
    #
    csn
    #
    ccnv
    #
    cuni
    #
    @13
    @6
    cC
    @4
    @17
    @0
    @1
    @5
    simprr
    @6
    @3
    @16
    @6
    @2
    @15
    @6
    cB
    @14
    @0
    @1
    cB
    @14
    wceq
    @5
    cB
    cA
    1st2nd
    adantrr
    #
    sneqd
    cnveqd
    unieqd
    eqtrd
    @12
    @11
    opswap
    syl6eq
    #
    @6
    @14
    cA
    wcel
    @13
    @7
    wcel
    @6
    cB
    @14
    cA
    @18
    @0
    @1
    @5
    simprl
    eqeltrrd
    @11
    @12
    cA
    cB
    c2nd
    fvex
    cB
    c1st
    fvex
    opelcnv
    sylibr
    eqeltrd
    @6
    @14
    @13
    csn
    #
    ccnv
    #
    cuni
    #
    cB
    @10
    @22
    @14
    @11
    @12
    opswap
    eqcomi
    @18
    @6
    @9
    @21
    @6
    @8
    @20
    @6
    cC
    @13
    @19
    sneqd
    cnveqd
    unieqd
    3eqtr4a
    jca
end
