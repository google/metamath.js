include "cch.mm"
include "wcel.mm"
include "w3a.mm"
include "ccm.mm"
include "wbr.mm"
include "wa.mm"
include "cin.mm"
include "chj.mm"
include "co.mm"
include "csh.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "c0h.mm"
include "wceq.mm"
include "chincl.mm"
include "chjcl.mm"
include "syl2an.mm"
include "anandis.mm"
include "sylan2.mm"
include "chsh.mm"
include "syl.mm"
include "jca.mm"
include "3impb.mm"
include "adantr.mm"
include "ledi.mm"
include "chdmj1.mm"
include "chdmm1.mm"
include "ineq1d.mm"
include "eqtrd.mm"
include "3impdi.mm"
include "ineq2d.mm"
include "in4.mm"
include "cmcm2.mm"
include "cmcm.mm"
include "wb.mm"
include "choccl.mm"
include "cmbr3.mm"
include "3bitr3d.mm"
include "biimpa.mm"
include "incom.mm"
include "syl6eq.mm"
include "3adantl3.mm"
include "adantrr.mm"
include "syl5eq.mm"
include "ococ.mm"
include "oveq1d.mm"
include "3ad2ant2.mm"
include "cmcm3.mm"
include "sylan.mm"
include "bitrd.mm"
include "3adantl1.mm"
include "adantrl.mm"
include "eqtr3d.mm"
include "inass.mm"
include "in12.mm"
include "eqtr4i.mm"
include "chocin.mm"
include "3adant2.mm"
include "chm0.mm"
include "pjoml.mm"
include "syl12anc.mm"
include "eqcomd.mm"

theorem fh2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. CH /\ B e. CH /\ C e. CH ) /\ ( B C_H A /\ B C_H C ) ) -> ( A i^i ( B vH C ) ) = ( ( A i^i B ) vH ( A i^i C ) ) )

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
    cB
    cA
    ccm
    wbr
    #
    cB
    cC
    ccm
    wbr
    #
    wa
    #
    wa
    #
    cA
    cB
    cin
    #
    cA
    cC
    cin
    #
    chj
    co
    #
    cA
    cB
    cC
    chj
    co
    #
    cin
    #
    @7
    @10
    cch
    wcel
    #
    @12
    csh
    wcel
    #
    wa
    #
    @10
    @12
    wss
    #
    @12
    @10
    cort
    cfv
    #
    cin
    #
    c0h
    wceq
    @10
    @12
    wceq
    @3
    @15
    @6
    @0
    @1
    @2
    @15
    @0
    @1
    @2
    wa
    #
    wa
    #
    @13
    @14
    @0
    @1
    @2
    @13
    @0
    @1
    wa
    #
    @8
    cch
    wcel
    #
    @9
    cch
    wcel
    #
    @13
    @0
    @2
    wa
    #
    cA
    cB
    chincl
    #
    cA
    cC
    chincl
    #
    @8
    @9
    chjcl
    syl2an
    anandis
    @20
    @12
    cch
    wcel
    #
    @14
    @19
    @0
    @11
    cch
    wcel
    @27
    cB
    cC
    chjcl
    cA
    @11
    chincl
    sylan2
    @12
    chsh
    syl
    jca
    3impb
    adantr
    @3
    @16
    @6
    cA
    cB
    cC
    ledi
    adantr
    @7
    @18
    cB
    cort
    cfv
    #
    @11
    cin
    #
    cA
    @9
    cort
    cfv
    #
    cin
    #
    cin
    #
    c0h
    @7
    @18
    @28
    cA
    cin
    #
    @11
    @30
    cin
    #
    cin
    #
    @32
    @7
    @18
    @12
    cA
    cort
    cfv
    @28
    chj
    co
    #
    @30
    cin
    #
    cin
    #
    @35
    @3
    @18
    @38
    wceq
    @6
    @3
    @17
    @37
    @12
    @0
    @1
    @2
    @17
    @37
    wceq
    @21
    @24
    wa
    #
    @17
    @8
    cort
    cfv
    #
    @30
    cin
    #
    @37
    @21
    @22
    @23
    @17
    @41
    wceq
    @24
    @25
    @26
    @8
    @9
    chdmj1
    syl2an
    @39
    @40
    @36
    @30
    @21
    @40
    @36
    wceq
    @24
    cA
    cB
    chdmm1
    adantr
    ineq1d
    eqtrd
    3impdi
    ineq2d
    adantr
    @7
    @38
    cA
    @36
    cin
    #
    @34
    cin
    @35
    cA
    @11
    @36
    @30
    in4
    @7
    @42
    @33
    @34
    @3
    @4
    @42
    @33
    wceq
    #
    @5
    @0
    @1
    @4
    @43
    @2
    @21
    @4
    wa
    @42
    cA
    @28
    cin
    #
    @33
    @21
    @4
    @42
    @44
    wceq
    #
    @21
    cA
    cB
    ccm
    wbr
    cA
    @28
    ccm
    wbr
    #
    @4
    @45
    cA
    cB
    cmcm2
    cA
    cB
    cmcm
    @1
    @0
    @28
    cch
    wcel
    #
    @46
    @45
    wb
    cB
    choccl
    #
    cA
    @28
    cmbr3
    sylan2
    3bitr3d
    biimpa
    cA
    @28
    incom
    syl6eq
    3adantl3
    adantrr
    ineq1d
    syl5eq
    eqtrd
    @28
    cA
    @11
    @30
    in4
    syl6eq
    @7
    @32
    @28
    cC
    cin
    #
    @31
    cin
    #
    c0h
    @7
    @29
    @49
    @31
    @7
    @28
    @28
    cort
    cfv
    #
    cC
    chj
    co
    #
    cin
    #
    @29
    @49
    @3
    @53
    @29
    wceq
    #
    @6
    @1
    @0
    @54
    @2
    @1
    @52
    @11
    @28
    @1
    @51
    cB
    cC
    chj
    cB
    ococ
    oveq1d
    ineq2d
    3ad2ant2
    adantr
    @3
    @5
    @53
    @49
    wceq
    #
    @4
    @1
    @2
    @5
    @55
    @0
    @19
    @5
    @55
    @19
    @5
    @28
    cC
    ccm
    wbr
    #
    @55
    cB
    cC
    cmcm3
    @1
    @47
    @2
    @56
    @55
    wb
    @48
    @28
    cC
    cmbr3
    sylan
    bitrd
    biimpa
    3adantl1
    adantrl
    eqtr3d
    ineq1d
    @3
    @50
    c0h
    wceq
    @6
    @3
    @50
    @28
    c0h
    cin
    #
    c0h
    @0
    @2
    @50
    @57
    wceq
    @1
    @24
    @50
    @28
    cC
    @31
    cin
    #
    cin
    @57
    @28
    cC
    @31
    inass
    @24
    @58
    c0h
    @28
    @24
    @58
    @9
    @30
    cin
    #
    c0h
    @58
    cA
    cC
    @30
    cin
    cin
    @59
    cC
    cA
    @30
    in12
    cA
    cC
    @30
    inass
    eqtr4i
    @24
    @23
    @59
    c0h
    wceq
    @26
    @9
    chocin
    syl
    syl5eq
    ineq2d
    syl5eq
    3adant2
    @1
    @0
    @57
    c0h
    wceq
    #
    @2
    @1
    @47
    @60
    @48
    @28
    chm0
    syl
    3ad2ant2
    eqtrd
    adantr
    eqtrd
    eqtrd
    @10
    @12
    pjoml
    syl12anc
    eqcomd
end
