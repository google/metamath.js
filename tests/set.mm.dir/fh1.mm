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
include "incom.mm"
include "a1i.mm"
include "chdmj1.mm"
include "chdmm1.mm"
include "ineqan12d.mm"
include "eqtrd.mm"
include "ineq12d.mm"
include "3impdi.mm"
include "inass.mm"
include "cmcm2.mm"
include "wb.mm"
include "choccl.mm"
include "cmbr3.mm"
include "bitrd.mm"
include "biimpa.mm"
include "3adantl3.mm"
include "adantrr.mm"
include "3adantl2.mm"
include "adantrl.mm"
include "inindi.mm"
include "3eqtr4g.mm"
include "ineq2d.mm"
include "syl5eq.mm"
include "in12.mm"
include "syl6eq.mm"
include "chocin.mm"
include "eqtr3d.mm"
include "chm0.mm"
include "sylan9eqr.mm"
include "pjoml.mm"
include "syl12anc.mm"
include "eqcomd.mm"

theorem fh1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. CH /\ B e. CH /\ C e. CH ) /\ ( A C_H B /\ A C_H C ) ) -> ( A i^i ( B vH C ) ) = ( ( A i^i B ) vH ( A i^i C ) ) )

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
    #
    @27
    cB
    cC
    chjcl
    #
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
    @11
    cA
    cin
    #
    cA
    cort
    cfv
    #
    cB
    cort
    cfv
    #
    chj
    co
    #
    @31
    cC
    cort
    cfv
    #
    chj
    co
    #
    cin
    #
    cin
    #
    c0h
    @3
    @18
    @37
    wceq
    #
    @6
    @0
    @1
    @2
    @38
    @21
    @24
    wa
    #
    @12
    @30
    @17
    @36
    @12
    @30
    wceq
    @39
    cA
    @11
    incom
    a1i
    @39
    @17
    @8
    cort
    cfv
    #
    @9
    cort
    cfv
    #
    cin
    #
    @36
    @21
    @22
    @23
    @17
    @42
    wceq
    @24
    @25
    @26
    @8
    @9
    chdmj1
    syl2an
    @21
    @24
    @40
    @33
    @41
    @35
    cA
    cB
    chdmm1
    cA
    cC
    chdmm1
    ineqan12d
    eqtrd
    ineq12d
    3impdi
    adantr
    @7
    @37
    cA
    @11
    @32
    @34
    cin
    #
    cin
    #
    cin
    #
    c0h
    @7
    @37
    @11
    cA
    @43
    cin
    #
    cin
    #
    @45
    @7
    @37
    @11
    cA
    @36
    cin
    #
    cin
    @47
    @11
    cA
    @36
    inass
    @7
    @48
    @46
    @11
    @7
    cA
    @33
    cin
    #
    cA
    @35
    cin
    #
    cin
    cA
    @32
    cin
    #
    cA
    @34
    cin
    #
    cin
    @48
    @46
    @7
    @49
    @51
    @50
    @52
    @3
    @4
    @49
    @51
    wceq
    #
    @5
    @0
    @1
    @4
    @53
    @2
    @21
    @4
    @53
    @21
    @4
    cA
    @32
    ccm
    wbr
    #
    @53
    cA
    cB
    cmcm2
    @1
    @0
    @32
    cch
    wcel
    @54
    @53
    wb
    cB
    choccl
    cA
    @32
    cmbr3
    sylan2
    bitrd
    biimpa
    3adantl3
    adantrr
    @3
    @5
    @50
    @52
    wceq
    #
    @4
    @0
    @2
    @5
    @55
    @1
    @24
    @5
    @55
    @24
    @5
    cA
    @34
    ccm
    wbr
    #
    @55
    cA
    cC
    cmcm2
    @2
    @0
    @34
    cch
    wcel
    @56
    @55
    wb
    cC
    choccl
    cA
    @34
    cmbr3
    sylan2
    bitrd
    biimpa
    3adantl2
    adantrl
    ineq12d
    cA
    @33
    @35
    inindi
    cA
    @32
    @34
    inindi
    3eqtr4g
    ineq2d
    syl5eq
    @11
    cA
    @43
    in12
    syl6eq
    @3
    @45
    c0h
    wceq
    #
    @6
    @0
    @1
    @2
    @57
    @19
    @0
    @45
    cA
    c0h
    cin
    c0h
    @19
    @44
    c0h
    cA
    @19
    @11
    @11
    cort
    cfv
    #
    cin
    #
    @44
    c0h
    @19
    @58
    @43
    @11
    cB
    cC
    chdmj1
    ineq2d
    @19
    @28
    @59
    c0h
    wceq
    @29
    @11
    chocin
    syl
    eqtr3d
    ineq2d
    cA
    chm0
    sylan9eqr
    3impb
    adantr
    eqtrd
    eqtrd
    @10
    @12
    pjoml
    syl12anc
    eqcomd
end
