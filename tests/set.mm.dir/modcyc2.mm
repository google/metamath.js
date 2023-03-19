include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "cz.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "cmo.mm"
include "cneg.mm"
include "caddc.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "rpcn.mm"
include "zcn.mm"
include "wa.mm"
include "mulneg1.mm"
include "ancoms.mm"
include "mulcom.mm"
include "negeqd.mm"
include "eqtr4d.mm"
include "3adant1.mm"
include "oveq2d.mm"
include "mulcl.mm"
include "negsub.mm"
include "sylan2.mm"
include "3impb.mm"
include "eqtr2d.mm"
include "syl3an.mm"
include "oveq1d.mm"
include "znegcl.mm"
include "modcyc.mm"
include "syl3an3.mm"
include "eqtrd.mm"

theorem modcyc2
  let cA: class A
  let cB: class B
  let cN: class N


  assert |- ( ( A e. RR /\ B e. RR+ /\ N e. ZZ ) -> ( ( A - ( B x. N ) ) mod B ) = ( A mod B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    crp
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cA
    cB
    cN
    cmul
    co
    #
    cmin
    co
    #
    cB
    cmo
    co
    cA
    cN
    cneg
    #
    cB
    cmul
    co
    #
    caddc
    co
    #
    cB
    cmo
    co
    #
    cA
    cB
    cmo
    co
    #
    @3
    @5
    @8
    cB
    cmo
    @0
    cA
    cc
    wcel
    #
    @1
    cB
    cc
    wcel
    #
    @2
    cN
    cc
    wcel
    #
    @5
    @8
    wceq
    cA
    recn
    cB
    rpcn
    cN
    zcn
    @11
    @12
    @13
    w3a
    #
    @8
    cA
    @4
    cneg
    #
    caddc
    co
    #
    @5
    @14
    @7
    @15
    cA
    caddc
    @12
    @13
    @7
    @15
    wceq
    @11
    @12
    @13
    wa
    #
    @7
    cN
    cB
    cmul
    co
    #
    cneg
    #
    @15
    @13
    @12
    @7
    @19
    wceq
    cN
    cB
    mulneg1
    ancoms
    @17
    @4
    @18
    cB
    cN
    mulcom
    negeqd
    eqtr4d
    3adant1
    oveq2d
    @11
    @12
    @13
    @16
    @5
    wceq
    #
    @17
    @11
    @4
    cc
    wcel
    @20
    cB
    cN
    mulcl
    cA
    @4
    negsub
    sylan2
    3impb
    eqtr2d
    syl3an
    oveq1d
    @2
    @0
    @1
    @6
    cz
    wcel
    @9
    @10
    wceq
    cN
    znegcl
    cA
    cB
    @6
    modcyc
    syl3an3
    eqtrd
end
