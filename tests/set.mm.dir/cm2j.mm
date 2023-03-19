include "cch.mm"
include "wcel.mm"
include "w3a.mm"
include "ccm.mm"
include "wbr.mm"
include "wa.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "cort.mm"
include "cfv.mm"
include "wceq.mm"
include "cmcm.mm"
include "wb.mm"
include "cmbr.mm"
include "ancoms.mm"
include "bitrd.mm"
include "biimpa.mm"
include "incom.mm"
include "oveq12i.mm"
include "syl6eq.mm"
include "3adantl3.mm"
include "adantrr.mm"
include "3adantl2.mm"
include "adantrl.mm"
include "oveq12d.mm"
include "chincl.mm"
include "choccl.mm"
include "sylan.mm"
include "jca.mm"
include "chj4.mm"
include "syl2an.mm"
include "3impdi.mm"
include "adantr.mm"
include "fh1.mm"
include "syl5reqr.mm"
include "3anim1i.mm"
include "cmcm3.mm"
include "3adant3.mm"
include "3adant2.mm"
include "anbi12d.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "ex.mm"
include "chjcl.mm"
include "sylan2.mm"
include "3impb.mm"
include "sylibrd.mm"
include "imp.mm"

theorem cm2j
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. CH /\ B e. CH /\ C e. CH ) /\ ( A C_H B /\ A C_H C ) ) -> A C_H ( B vH C ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    cC
    cch
    wcel
    #
    w3a
    #
    cA
    cB
    ccm
    wbr
    #
    cA
    cC
    ccm
    wbr
    #
    wa
    #
    cA
    cB
    cC
    chj
    co
    #
    ccm
    wbr
    #
    @3
    @6
    @7
    @7
    cA
    cin
    #
    @7
    cA
    cort
    cfv
    #
    cin
    #
    chj
    co
    #
    wceq
    #
    @8
    @3
    @6
    @13
    @3
    @6
    wa
    #
    @7
    cA
    cB
    cin
    #
    @10
    cB
    cin
    #
    chj
    co
    #
    cA
    cC
    cin
    #
    @10
    cC
    cin
    #
    chj
    co
    #
    chj
    co
    #
    @15
    @18
    chj
    co
    #
    @16
    @19
    chj
    co
    #
    chj
    co
    #
    @12
    @14
    cB
    @17
    cC
    @20
    chj
    @3
    @4
    cB
    @17
    wceq
    #
    @5
    @0
    @1
    @4
    @25
    @2
    @0
    @1
    wa
    #
    @4
    wa
    cB
    cB
    cA
    cin
    #
    cB
    @10
    cin
    #
    chj
    co
    #
    @17
    @26
    @4
    cB
    @29
    wceq
    #
    @26
    @4
    cB
    cA
    ccm
    wbr
    #
    @30
    cA
    cB
    cmcm
    @1
    @0
    @31
    @30
    wb
    cB
    cA
    cmbr
    ancoms
    bitrd
    biimpa
    @27
    @15
    @28
    @16
    chj
    cB
    cA
    incom
    cB
    @10
    incom
    oveq12i
    syl6eq
    3adantl3
    adantrr
    @3
    @5
    cC
    @20
    wceq
    #
    @4
    @0
    @2
    @5
    @32
    @1
    @0
    @2
    wa
    #
    @5
    wa
    cC
    cC
    cA
    cin
    #
    cC
    @10
    cin
    #
    chj
    co
    #
    @20
    @33
    @5
    cC
    @36
    wceq
    #
    @33
    @5
    cC
    cA
    ccm
    wbr
    #
    @37
    cA
    cC
    cmcm
    @2
    @0
    @38
    @37
    wb
    cC
    cA
    cmbr
    ancoms
    bitrd
    biimpa
    @34
    @18
    @35
    @19
    chj
    cC
    cA
    incom
    cC
    @10
    incom
    oveq12i
    syl6eq
    3adantl2
    adantrl
    oveq12d
    @3
    @21
    @24
    wceq
    #
    @6
    @0
    @1
    @2
    @39
    @26
    @15
    cch
    wcel
    #
    @16
    cch
    wcel
    #
    wa
    @18
    cch
    wcel
    #
    @19
    cch
    wcel
    #
    wa
    @39
    @33
    @26
    @40
    @41
    cA
    cB
    chincl
    @0
    @10
    cch
    wcel
    #
    @1
    @41
    cA
    choccl
    #
    @10
    cB
    chincl
    sylan
    jca
    @33
    @42
    @43
    cA
    cC
    chincl
    @0
    @44
    @2
    @43
    @45
    @10
    cC
    chincl
    sylan
    jca
    @15
    @16
    @18
    @19
    chj4
    syl2an
    3impdi
    adantr
    @14
    @22
    @9
    @23
    @11
    chj
    @14
    @9
    cA
    @7
    cin
    @22
    cA
    @7
    incom
    cA
    cB
    cC
    fh1
    syl5reqr
    @14
    @11
    @10
    @7
    cin
    #
    @23
    @10
    @7
    incom
    @14
    @44
    @1
    @2
    w3a
    #
    @10
    cB
    ccm
    wbr
    #
    @10
    cC
    ccm
    wbr
    #
    wa
    #
    @46
    @23
    wceq
    @3
    @47
    @6
    @0
    @44
    @1
    @2
    @45
    3anim1i
    adantr
    @3
    @6
    @50
    @3
    @4
    @48
    @5
    @49
    @0
    @1
    @4
    @48
    wb
    @2
    cA
    cB
    cmcm3
    3adant3
    @0
    @2
    @5
    @49
    wb
    @1
    cA
    cC
    cmcm3
    3adant2
    anbi12d
    biimpa
    @10
    cB
    cC
    fh1
    syl2anc
    syl5reqr
    oveq12d
    3eqtrd
    ex
    @0
    @1
    @2
    @8
    @13
    wb
    #
    @1
    @2
    wa
    @0
    @7
    cch
    wcel
    #
    @51
    cB
    cC
    chjcl
    @0
    @52
    wa
    @8
    @7
    cA
    ccm
    wbr
    #
    @13
    cA
    @7
    cmcm
    @52
    @0
    @53
    @13
    wb
    @7
    cA
    cmbr
    ancoms
    bitrd
    sylan2
    3impb
    sylibrd
    imp
end
