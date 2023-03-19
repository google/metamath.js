include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "c2.mm"
include "c3.mm"
include "cun.mm"
include "cop.mm"
include "wf1o.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cz.mm"
include "simpl.mm"
include "0z.mm"
include "jctil.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "1z.mm"
include "jca.mm"
include "id.mm"
include "3ad2ant1.mm"
include "0ne1.mm"
include "adantr.mm"
include "adantl.mm"
include "f1oprg.mm"
include "sylc.mm"
include "cn.mm"
include "2nn.mm"
include "3nn.mm"
include "3ad2ant3.mm"
include "2re.mm"
include "2lt3.mm"
include "ltneii.mm"
include "csn.mm"
include "disjsn2.mm"
include "3ad2ant2.mm"
include "anim12i.mm"
include "df-pr.mm"
include "ineq1i.mm"
include "eqeq1i.mm"
include "undisj1.mm"
include "bitr4i.mm"
include "sylibr.mm"
include "undisj2.mm"
include "eqcomi.mm"
include "ineq2i.mm"
include "bitri.mm"
include "sylib.mm"
include "0ne2.mm"
include "ax-mp.mm"
include "1ne2.mm"
include "pm3.2i.mm"
include "mpbi.mm"
include "eqtr3i.mm"
include "3ne0.mm"
include "necomi.mm"
include "1re.mm"
include "1lt3.mm"
include "f1oun.mm"
include "syl21anc.mm"
include "ex.mm"

theorem f1oun2prg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y


  assert |- ( ( ( A e. V /\ B e. W ) /\ ( C e. X /\ D e. Y ) ) -> ( ( ( A =/= B /\ A =/= C /\ A =/= D ) /\ ( B =/= C /\ B =/= D /\ C =/= D ) ) -> ( { <. 0 , A >. , <. 1 , B >. } u. { <. 2 , C >. , <. 3 , D >. } ) : ( { 0 , 1 } u. { 2 , 3 } ) -1-1-onto-> ( { A , B } u. { C , D } ) ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    cC
    cX
    wcel
    #
    cD
    cY
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    wne
    #
    cA
    cC
    wne
    #
    cA
    cD
    wne
    #
    w3a
    #
    cB
    cC
    wne
    #
    cB
    cD
    wne
    #
    cC
    cD
    wne
    #
    w3a
    #
    wa
    #
    cc0
    c1
    cpr
    #
    c2
    c3
    cpr
    #
    cun
    cA
    cB
    cpr
    #
    cC
    cD
    cpr
    #
    cun
    cc0
    cA
    cop
    c1
    cB
    cop
    cpr
    #
    c2
    cC
    cop
    c3
    cD
    cop
    cpr
    #
    cun
    wf1o
    #
    @6
    @15
    wa
    #
    @16
    @18
    @20
    wf1o
    #
    @17
    @19
    @21
    wf1o
    #
    @16
    @17
    cin
    #
    c0
    wceq
    #
    @18
    @19
    cin
    #
    c0
    wceq
    #
    wa
    @22
    @23
    cc0
    cz
    wcel
    #
    @0
    wa
    #
    c1
    cz
    wcel
    #
    @1
    wa
    #
    wa
    cc0
    c1
    wne
    #
    @7
    wa
    #
    @24
    @23
    @31
    @33
    @2
    @31
    @5
    @15
    @2
    @0
    @30
    @0
    @1
    simpl
    0z
    jctil
    ad2antrr
    @2
    @33
    @5
    @15
    @2
    @1
    @32
    @0
    @1
    simpr
    1z
    jctil
    ad2antrr
    jca
    @15
    @35
    @6
    @10
    @35
    @14
    @10
    @7
    @34
    @7
    @8
    @7
    @9
    @7
    id
    3ad2ant1
    0ne1
    jctil
    adantr
    adantl
    cc0
    cA
    c1
    cB
    cz
    cV
    cz
    cW
    f1oprg
    sylc
    @23
    c2
    cn
    wcel
    #
    @3
    wa
    #
    c3
    cn
    wcel
    #
    @4
    wa
    #
    wa
    #
    c2
    c3
    wne
    #
    @13
    wa
    #
    @25
    @6
    @40
    @15
    @6
    @37
    @39
    @5
    @37
    @2
    @5
    @3
    @36
    @3
    @4
    simpl
    2nn
    jctil
    adantl
    @5
    @39
    @2
    @5
    @4
    @38
    @3
    @4
    simpr
    3nn
    jctil
    adantl
    jca
    adantr
    @15
    @42
    @6
    @14
    @42
    @10
    @14
    @13
    @41
    @13
    @11
    @13
    @12
    @13
    id
    3ad2ant3
    c2
    c3
    2re
    2lt3
    ltneii
    jctil
    adantl
    adantl
    c2
    cC
    c3
    cD
    cn
    cX
    cn
    cY
    f1oprg
    sylc
    @23
    @29
    @27
    @23
    @18
    cC
    csn
    #
    cin
    #
    c0
    wceq
    #
    @18
    cD
    csn
    #
    cin
    #
    c0
    wceq
    #
    wa
    #
    @29
    @23
    @45
    @48
    @23
    cA
    csn
    #
    @43
    cin
    c0
    wceq
    #
    cB
    csn
    #
    @43
    cin
    c0
    wceq
    #
    wa
    #
    @45
    @15
    @54
    @6
    @10
    @51
    @14
    @53
    @8
    @7
    @51
    @9
    cA
    cC
    disjsn2
    3ad2ant2
    @11
    @12
    @53
    @13
    cB
    cC
    disjsn2
    3ad2ant1
    anim12i
    adantl
    @45
    @50
    @52
    cun
    #
    @43
    cin
    #
    c0
    wceq
    @54
    @44
    @56
    c0
    @18
    @55
    @43
    cA
    cB
    df-pr
    #
    ineq1i
    eqeq1i
    @50
    @52
    @43
    undisj1
    bitr4i
    sylibr
    @23
    @50
    @46
    cin
    c0
    wceq
    #
    @52
    @46
    cin
    c0
    wceq
    #
    wa
    #
    @48
    @15
    @60
    @6
    @10
    @58
    @14
    @59
    @9
    @7
    @58
    @8
    cA
    cD
    disjsn2
    3ad2ant3
    @12
    @11
    @59
    @13
    cB
    cD
    disjsn2
    3ad2ant2
    anim12i
    adantl
    @48
    @55
    @46
    cin
    #
    c0
    wceq
    @60
    @47
    @61
    c0
    @18
    @55
    @46
    @57
    ineq1i
    eqeq1i
    @50
    @52
    @46
    undisj1
    bitr4i
    sylibr
    jca
    @49
    @18
    @43
    @46
    cun
    #
    cin
    #
    c0
    wceq
    @29
    @18
    @43
    @46
    undisj2
    @63
    @28
    c0
    @62
    @19
    @18
    @19
    @62
    cC
    cD
    df-pr
    eqcomi
    ineq2i
    eqeq1i
    bitri
    sylib
    @16
    c2
    csn
    #
    cin
    #
    c0
    wceq
    #
    @16
    c3
    csn
    #
    cin
    #
    c0
    wceq
    #
    wa
    #
    @27
    @66
    @69
    cc0
    csn
    #
    c1
    csn
    #
    cun
    #
    @64
    cin
    #
    @65
    c0
    @73
    @16
    @64
    @16
    @73
    cc0
    c1
    df-pr
    eqcomi
    #
    ineq1i
    @71
    @64
    cin
    c0
    wceq
    #
    @72
    @64
    cin
    c0
    wceq
    #
    wa
    @74
    c0
    wceq
    @76
    @77
    cc0
    c2
    wne
    @76
    0ne2
    cc0
    c2
    disjsn2
    ax-mp
    c1
    c2
    wne
    @77
    1ne2
    c1
    c2
    disjsn2
    ax-mp
    pm3.2i
    @71
    @72
    @64
    undisj1
    mpbi
    eqtr3i
    @73
    @67
    cin
    #
    @68
    c0
    @73
    @16
    @67
    @75
    ineq1i
    @71
    @67
    cin
    c0
    wceq
    #
    @72
    @67
    cin
    c0
    wceq
    #
    wa
    @78
    c0
    wceq
    @79
    @80
    cc0
    c3
    wne
    @79
    c3
    cc0
    3ne0
    necomi
    cc0
    c3
    disjsn2
    ax-mp
    c1
    c3
    wne
    @80
    c1
    c3
    1re
    1lt3
    ltneii
    c1
    c3
    disjsn2
    ax-mp
    pm3.2i
    @71
    @72
    @67
    undisj1
    mpbi
    eqtr3i
    pm3.2i
    @70
    @16
    @64
    @67
    cun
    #
    cin
    #
    c0
    wceq
    @27
    @16
    @64
    @67
    undisj2
    @82
    @26
    c0
    @81
    @17
    @16
    @17
    @81
    c2
    c3
    df-pr
    eqcomi
    ineq2i
    eqeq1i
    bitri
    mpbi
    jctil
    @16
    @18
    @17
    @19
    @20
    @21
    f1oun
    syl21anc
    ex
end
