include "cz.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cfzo.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "simpl.mm"
include "fzolb.mm"
include "sylibr.mm"
include "simpr.mm"
include "eleqtrd.mm"
include "elfzouz.mm"
include "uzss.mm"
include "3syl.mm"
include "biimpri.mm"
include "adantr.mm"
include "wb.mm"
include "eleq2.mm"
include "adantl.mm"
include "mpbid.mm"
include "elfzolt3b.mm"
include "syl.mm"
include "eleqtrrd.mm"
include "eqssd.mm"
include "simpl1.mm"
include "uz11.mm"
include "cle.mm"
include "c1.mm"
include "cmin.mm"
include "wi.mm"
include "fzoend.mm"
include "elfzoel2.mm"
include "eqcoms.mm"
include "elfzo2.mm"
include "simprl.mm"
include "zlem1lt.mm"
include "ancoms.mm"
include "biimprd.mm"
include "impancom.mm"
include "impcom.mm"
include "3jca.mm"
include "expcom.mm"
include "3adant1.mm"
include "a1d.mm"
include "sylbi.mm"
include "syl6bi.mm"
include "com23.mm"
include "com13.mm"
include "mpcom.mm"
include "eluz2.mm"
include "pm3.2.mm"
include "3ad2ant2.mm"
include "com12.mm"
include "com3l.mm"
include "imp.mm"
include "syl3anbrc.mm"
include "simpl2.mm"
include "jca.mm"
include "ex.mm"
include "oveq12.mm"
include "impbid1.mm"

theorem fzoopth
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( M e. ZZ /\ N e. ZZ /\ M < N ) -> ( ( M ..^ N ) = ( J ..^ K ) <-> ( M = J /\ N = K ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cM
    cN
    clt
    wbr
    #
    w3a
    #
    cM
    cN
    cfzo
    co
    #
    cJ
    cK
    cfzo
    co
    #
    wceq
    #
    cM
    cJ
    wceq
    #
    cN
    cK
    wceq
    #
    wa
    #
    @3
    @6
    @9
    @3
    @6
    wa
    #
    @7
    @8
    @10
    cM
    cuz
    cfv
    #
    cJ
    cuz
    cfv
    #
    wceq
    #
    @7
    @10
    @11
    @12
    @10
    cM
    @5
    wcel
    #
    cM
    @12
    wcel
    @11
    @12
    wss
    @10
    cM
    @4
    @5
    @10
    @3
    cM
    @4
    wcel
    #
    @3
    @6
    simpl
    cM
    cN
    fzolb
    #
    sylibr
    @3
    @6
    simpr
    #
    eleqtrd
    cM
    cJ
    cK
    elfzouz
    cJ
    cM
    uzss
    3syl
    @10
    cJ
    @4
    wcel
    cJ
    @11
    wcel
    @12
    @11
    wss
    @10
    cJ
    @5
    @4
    @10
    @14
    cJ
    @5
    wcel
    #
    @10
    @15
    @14
    @3
    @15
    @6
    @15
    @3
    @16
    biimpri
    #
    adantr
    @6
    @15
    @14
    wb
    @3
    @4
    @5
    cM
    eleq2
    adantl
    mpbid
    cM
    cJ
    cK
    elfzolt3b
    syl
    #
    @17
    eleqtrrd
    cJ
    cM
    cN
    elfzouz
    cM
    cJ
    uzss
    3syl
    eqssd
    @10
    @0
    @13
    @7
    wb
    @0
    @1
    @2
    @6
    simpl1
    cM
    cJ
    uz11
    syl
    mpbid
    @10
    cN
    cuz
    cfv
    #
    cK
    cuz
    cfv
    #
    wceq
    #
    @8
    @10
    @21
    @22
    @10
    cK
    cz
    wcel
    #
    @1
    cK
    cN
    cle
    wbr
    #
    w3a
    #
    cN
    @22
    wcel
    #
    @21
    @22
    wss
    @18
    @10
    @26
    @20
    @18
    cK
    c1
    cmin
    co
    #
    @5
    wcel
    #
    @10
    @26
    wi
    #
    cJ
    cK
    fzoend
    @24
    @29
    @30
    @28
    cJ
    cK
    elfzoel2
    @10
    @29
    @24
    @26
    @6
    @3
    @29
    @24
    @26
    wi
    #
    wi
    @6
    @29
    @3
    @31
    @6
    @29
    @28
    @4
    wcel
    #
    @3
    @31
    wi
    #
    @29
    @32
    wb
    @5
    @4
    @5
    @4
    @28
    eleq2
    eqcoms
    @32
    @28
    @11
    wcel
    #
    @1
    @28
    cN
    clt
    wbr
    #
    w3a
    #
    @33
    @28
    cM
    cN
    elfzo2
    @36
    @31
    @3
    @1
    @35
    @31
    @34
    @24
    @1
    @35
    wa
    #
    @26
    @24
    @37
    wa
    @24
    @1
    @25
    @24
    @37
    simpl
    @24
    @1
    @35
    simprl
    @37
    @24
    @25
    @1
    @24
    @35
    @25
    @1
    @24
    wa
    @25
    @35
    @24
    @1
    @25
    @35
    wb
    cK
    cN
    zlem1lt
    ancoms
    biimprd
    impancom
    impcom
    3jca
    expcom
    3adant1
    a1d
    sylbi
    syl6bi
    com23
    impcom
    com13
    mpcom
    syl
    mpcom
    @27
    @26
    cK
    cN
    eluz2
    biimpri
    cK
    cN
    uzss
    3syl
    @10
    @1
    @24
    cN
    c1
    cmin
    co
    #
    cK
    clt
    wbr
    #
    wa
    #
    wa
    #
    cK
    @21
    wcel
    #
    @22
    @21
    wss
    @3
    @6
    @41
    @15
    @3
    @6
    @41
    wi
    #
    @19
    @15
    @38
    @4
    wcel
    #
    @3
    @43
    wi
    cM
    cN
    fzoend
    @6
    @44
    @3
    @41
    @6
    @44
    @38
    @5
    wcel
    #
    @3
    @41
    wi
    #
    @4
    @5
    @38
    eleq2
    @45
    @38
    @12
    wcel
    #
    @24
    @39
    w3a
    @46
    @38
    cJ
    cK
    elfzo2
    @24
    @39
    @46
    @47
    @3
    @40
    @41
    @1
    @0
    @40
    @41
    wi
    @2
    @1
    @40
    pm3.2
    3ad2ant2
    com12
    3adant1
    sylbi
    syl6bi
    com3l
    syl
    mpcom
    imp
    @41
    @1
    @24
    cN
    cK
    cle
    wbr
    #
    @42
    @1
    @40
    simpl
    @1
    @24
    @39
    simprl
    @40
    @1
    @48
    @24
    @1
    @39
    @48
    @24
    @1
    wa
    @48
    @39
    @1
    @24
    @48
    @39
    wb
    cN
    cK
    zlem1lt
    ancoms
    biimprd
    impancom
    impcom
    cN
    cK
    eluz2
    syl3anbrc
    cN
    cK
    uzss
    3syl
    eqssd
    @10
    @1
    @23
    @8
    wb
    @0
    @1
    @2
    @6
    simpl2
    cN
    cK
    uz11
    syl
    mpbid
    jca
    ex
    cM
    cJ
    cN
    cK
    cfzo
    oveq12
    impbid1
end
