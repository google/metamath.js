include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "w3a.mm"
include "cmo.mm"
include "co.mm"
include "caddc.mm"
include "cc.mm"
include "wa.mm"
include "modcl.mm"
include "recnd.mm"
include "3adant2.mm"
include "3adant1.mm"
include "addcomd.mm"
include "oveq1d.mm"
include "wceq.mm"
include "simpl.mm"
include "jca.mm"
include "simpr.mm"
include "modabs2.mm"
include "modadd1.mm"
include "syl3anc.mm"
include "recn.mm"
include "3ad2ant2.mm"
include "eqtr4d.mm"
include "3simpc.mm"
include "3eqtrd.mm"

theorem modaddabs
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR+ ) -> ( ( ( A mod C ) + ( B mod C ) ) mod C ) = ( ( A + B ) mod C ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cC
    crp
    wcel
    #
    w3a
    #
    cA
    cC
    cmo
    co
    #
    cB
    cC
    cmo
    co
    #
    caddc
    co
    #
    cC
    cmo
    co
    @5
    @4
    caddc
    co
    #
    cC
    cmo
    co
    #
    @4
    cB
    caddc
    co
    #
    cC
    cmo
    co
    #
    cA
    cB
    caddc
    co
    cC
    cmo
    co
    #
    @3
    @6
    @7
    cC
    cmo
    @3
    @4
    @5
    @0
    @2
    @4
    cc
    wcel
    @1
    @0
    @2
    wa
    #
    @4
    cA
    cC
    modcl
    #
    recnd
    3adant2
    #
    @1
    @2
    @5
    cc
    wcel
    @0
    @1
    @2
    wa
    #
    @5
    cB
    cC
    modcl
    #
    recnd
    3adant1
    addcomd
    oveq1d
    @3
    @8
    cB
    @4
    caddc
    co
    #
    cC
    cmo
    co
    #
    @10
    @3
    @5
    cr
    wcel
    #
    @1
    wa
    #
    @4
    cr
    wcel
    #
    @2
    wa
    #
    @5
    cC
    cmo
    co
    @5
    wceq
    #
    @8
    @18
    wceq
    @1
    @2
    @20
    @0
    @15
    @19
    @1
    @16
    @1
    @2
    simpl
    jca
    3adant1
    @0
    @2
    @22
    @1
    @12
    @21
    @2
    @13
    @0
    @2
    simpr
    jca
    3adant2
    @1
    @2
    @23
    @0
    cB
    cC
    modabs2
    3adant1
    @5
    cB
    @4
    cC
    modadd1
    syl3anc
    @3
    @9
    @17
    cC
    cmo
    @3
    @4
    cB
    @14
    @1
    @0
    cB
    cc
    wcel
    @2
    cB
    recn
    3ad2ant2
    addcomd
    oveq1d
    eqtr4d
    @3
    @21
    @0
    wa
    #
    @15
    @4
    cC
    cmo
    co
    @4
    wceq
    #
    @10
    @11
    wceq
    @0
    @2
    @24
    @1
    @12
    @21
    @0
    @13
    @0
    @2
    simpl
    jca
    3adant2
    @0
    @1
    @2
    3simpc
    @0
    @2
    @25
    @1
    cA
    cC
    modabs2
    3adant2
    @4
    cA
    cB
    cC
    modadd1
    syl3anc
    3eqtrd
end
