include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "wceq.mm"
include "cn0.mm"
include "wcel.mm"
include "w3a.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "cxp.mm"
include "crelexp.mm"
include "co.mm"
include "wi.mm"
include "cn.mm"
include "cc0.mm"
include "wo.mm"
include "elnn0.mm"
include "wa.mm"
include "ifeqor.mm"
include "andi.mm"
include "biimpi.mm"
include "mpan2.mm"
include "eqtr.mm"
include "orim12i.mm"
include "relexpxpnnidm.mm"
include "imp.mm"
include "3ad2antl3.mm"
include "3ad2antl2.mm"
include "oveq1d.mm"
include "simpl1.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "3exp1.mm"
include "eqcomd.mm"
include "oveq12d.mm"
include "jaoi.mm"
include "3syl.mm"
include "com13.mm"
include "simp3.mm"
include "simp2.mm"
include "simp1.mm"
include "nngt0d.mm"
include "eqbrtrd.mm"
include "iftrued.mm"
include "3eqtrd.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "cvv.mm"
include "simpr1.mm"
include "simpr2.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "dmexg.mm"
include "rnexg.mm"
include "jca.mm"
include "unexg.mm"
include "nnnn0d.mm"
include "relexpiidm.mm"
include "simpl2.mm"
include "relexp0g.mm"
include "syl.mm"
include "simpl3.mm"
include "ex.mm"
include "syld3an3.mm"
include "3exp.mm"
include "jaod.mm"
include "syl5bi.mm"
include "3ad2ant2.mm"
include "wn.mm"
include "nn0nlt0.mm"
include "breq2d.mm"
include "mtbird.mm"
include "iffalsed.mm"
include "relexp0idm.mm"
include "syl3c.mm"
include "sylbi.mm"
include "3imp.mm"
include "impcom.mm"

theorem relexpxpmin
  let cA: class A
  let cB: class B
  let cU: class U
  let cI: class I
  let cJ: class J
  let cK: class K
  let cV: class V


  assert |- ( ( ( A e. U /\ B e. V /\ ( A i^i B ) =/= (/) ) /\ ( I = if ( J < K , J , K ) /\ J e. NN0 /\ K e. NN0 ) ) -> ( ( ( A X. B ) ^r J ) ^r K ) = ( ( A X. B ) ^r I ) )

  proof
    cI
    cJ
    cK
    clt
    wbr
    #
    cJ
    cK
    cif
    #
    wceq
    #
    cJ
    cn0
    wcel
    #
    cK
    cn0
    wcel
    #
    w3a
    cA
    cU
    wcel
    #
    cB
    cV
    wcel
    #
    cA
    cB
    cin
    c0
    wne
    #
    w3a
    #
    cA
    cB
    cxp
    #
    cJ
    crelexp
    co
    #
    cK
    crelexp
    co
    #
    @9
    cI
    crelexp
    co
    #
    wceq
    #
    @2
    @3
    @4
    @8
    @13
    wi
    #
    @4
    @3
    @2
    @14
    @4
    cK
    cn
    wcel
    #
    cK
    cc0
    wceq
    #
    wo
    @3
    @2
    @14
    wi
    #
    wi
    #
    cK
    elnn0
    @15
    @18
    @16
    @3
    cJ
    cn
    wcel
    #
    cJ
    cc0
    wceq
    #
    wo
    #
    @15
    @17
    cJ
    elnn0
    #
    @15
    @19
    @17
    @20
    @2
    @19
    @15
    @14
    @2
    @2
    @1
    cJ
    wceq
    #
    wa
    #
    @2
    @1
    cK
    wceq
    #
    wa
    #
    wo
    #
    cI
    cJ
    wceq
    #
    cI
    cK
    wceq
    #
    wo
    @19
    @15
    @14
    wi
    wi
    #
    @2
    @23
    @25
    wo
    #
    @27
    @0
    cJ
    cK
    ifeqor
    @2
    @31
    wa
    @27
    @2
    @23
    @25
    andi
    biimpi
    mpan2
    @24
    @28
    @26
    @29
    cI
    @1
    cJ
    eqtr
    cI
    @1
    cK
    eqtr
    orim12i
    @28
    @30
    @29
    @28
    @19
    @15
    @8
    @13
    @28
    @19
    @15
    w3a
    @8
    wa
    #
    @9
    cK
    crelexp
    co
    #
    @9
    @11
    @12
    @15
    @28
    @8
    @33
    @9
    wceq
    #
    @19
    @15
    @8
    @34
    cA
    cB
    cU
    cK
    cV
    relexpxpnnidm
    imp
    3ad2antl3
    @32
    @10
    @9
    cK
    crelexp
    @19
    @28
    @8
    @10
    @9
    wceq
    #
    @15
    @19
    @8
    @35
    cA
    cB
    cU
    cJ
    cV
    relexpxpnnidm
    #
    imp
    #
    3ad2antl2
    #
    oveq1d
    @32
    @12
    @10
    @9
    @32
    cI
    cJ
    @9
    crelexp
    @28
    @19
    @15
    @8
    simpl1
    oveq2d
    @38
    eqtrd
    3eqtr4d
    3exp1
    @29
    @19
    @15
    @8
    @13
    @29
    @19
    @15
    w3a
    @8
    wa
    #
    @10
    @9
    cK
    cI
    crelexp
    @19
    @29
    @8
    @35
    @15
    @37
    3ad2antl2
    @39
    cI
    cK
    @29
    @19
    @15
    @8
    simpl1
    eqcomd
    oveq12d
    3exp1
    jaoi
    3syl
    com13
    @15
    @20
    @2
    @14
    @15
    @20
    @2
    cI
    cc0
    wceq
    #
    @14
    @15
    @20
    @2
    w3a
    #
    cI
    @1
    cJ
    cc0
    @15
    @20
    @2
    simp3
    @41
    @0
    cJ
    cK
    @41
    cJ
    cc0
    cK
    clt
    @15
    @20
    @2
    simp2
    #
    @41
    cK
    @15
    @20
    @2
    simp1
    nngt0d
    eqbrtrd
    iftrued
    @42
    3eqtrd
    @15
    @20
    @40
    w3a
    #
    @8
    @13
    @43
    @8
    wa
    #
    cid
    @9
    cdm
    #
    @9
    crn
    #
    cun
    #
    cres
    #
    cK
    crelexp
    co
    #
    @48
    @11
    @12
    @44
    @47
    cvv
    wcel
    #
    @4
    @49
    @48
    wceq
    @44
    @9
    cvv
    wcel
    #
    @45
    cvv
    wcel
    #
    @46
    cvv
    wcel
    #
    wa
    @50
    @44
    @5
    @6
    @51
    @43
    @5
    @6
    @7
    simpr1
    @43
    @5
    @6
    @7
    simpr2
    cA
    cB
    cU
    cV
    xpexg
    #
    syl2anc
    #
    @51
    @52
    @53
    @9
    cvv
    dmexg
    @9
    cvv
    rnexg
    jca
    @45
    @46
    cvv
    cvv
    unexg
    3syl
    @44
    cK
    @15
    @20
    @40
    @8
    simpl1
    nnnn0d
    @47
    cK
    cvv
    relexpiidm
    syl2anc
    @44
    @10
    @48
    cK
    crelexp
    @44
    @10
    @9
    cc0
    crelexp
    co
    #
    @48
    @44
    cJ
    cc0
    @9
    crelexp
    @15
    @20
    @40
    @8
    simpl2
    oveq2d
    @44
    @51
    @56
    @48
    wceq
    @55
    @9
    cvv
    relexp0g
    syl
    #
    eqtrd
    oveq1d
    @44
    @12
    @56
    @48
    @44
    cI
    cc0
    @9
    crelexp
    @15
    @20
    @40
    @8
    simpl3
    oveq2d
    @57
    eqtrd
    3eqtr4d
    ex
    syld3an3
    3exp
    jaod
    syl5bi
    @16
    @3
    @2
    @14
    @16
    @3
    @2
    w3a
    #
    @16
    @21
    @40
    @14
    @16
    @3
    @2
    simp1
    #
    @3
    @16
    @21
    @2
    @3
    @21
    @22
    biimpi
    3ad2ant2
    @58
    cI
    @1
    cK
    cc0
    @16
    @3
    @2
    simp3
    @58
    @0
    cJ
    cK
    @58
    @0
    cJ
    cc0
    clt
    wbr
    #
    @3
    @16
    @60
    wn
    @2
    cJ
    nn0nlt0
    3ad2ant2
    @58
    cK
    cc0
    cJ
    clt
    @59
    breq2d
    mtbird
    iffalsed
    @59
    3eqtrd
    @16
    @19
    @40
    @14
    wi
    @20
    @16
    @19
    @40
    @8
    @13
    @16
    @19
    @40
    w3a
    #
    @8
    wa
    #
    @10
    cc0
    crelexp
    co
    @56
    @11
    @12
    @62
    @10
    @9
    cc0
    crelexp
    @61
    @8
    @35
    @19
    @16
    @8
    @35
    wi
    @40
    @36
    3ad2ant2
    imp
    oveq1d
    @62
    cK
    cc0
    @10
    crelexp
    @16
    @19
    @40
    @8
    simpl1
    oveq2d
    @62
    cI
    cc0
    @9
    crelexp
    @16
    @19
    @40
    @8
    simpl3
    oveq2d
    3eqtr4d
    3exp1
    @16
    @20
    @40
    @8
    @13
    @16
    @20
    @40
    w3a
    #
    @8
    wa
    #
    @56
    cc0
    crelexp
    co
    #
    @56
    @11
    @12
    @64
    @51
    @65
    @56
    wceq
    @64
    @5
    @6
    @51
    @63
    @5
    @6
    @7
    simpr1
    @63
    @5
    @6
    @7
    simpr2
    @54
    syl2anc
    @9
    cvv
    relexp0idm
    syl
    @64
    @10
    @56
    cK
    cc0
    crelexp
    @64
    cJ
    cc0
    @9
    crelexp
    @16
    @20
    @40
    @8
    simpl2
    oveq2d
    @16
    @20
    @40
    @8
    simpl1
    oveq12d
    @64
    cI
    cc0
    @9
    crelexp
    @16
    @20
    @40
    @8
    simpl3
    oveq2d
    3eqtr4d
    3exp1
    jaod
    syl3c
    3exp
    jaoi
    sylbi
    com13
    3imp
    impcom
end
