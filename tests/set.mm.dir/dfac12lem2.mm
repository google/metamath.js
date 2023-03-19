include "cr1.mm"
include "cfv.mm"
include "con0.mm"
include "wf1.mm"
include "cuni.mm"
include "wceq.mm"
include "cima.mm"
include "crn.mm"
include "csuc.mm"
include "cv.mm"
include "crnk.mm"
include "comu.mm"
include "co.mm"
include "coa.mm"
include "cif.mm"
include "cmpt.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "wss.mm"
include "wfun.mm"
include "wfn.mm"
include "cdm.mm"
include "cep.mm"
include "coi.mm"
include "ccnv.mm"
include "ccom.mm"
include "tfr1.mm"
include "fnfun.mm"
include "ax-mp.mm"
include "funimaexg.mm"
include "sylancr.mm"
include "uniexg.mm"
include "rnexg.mm"
include "3syl.mm"
include "cxp.mm"
include "cpw.mm"
include "wral.mm"
include "wf.mm"
include "f1f.mm"
include "fssxp.mm"
include "ssv.mm"
include "xpss1.mm"
include "sstr.mm"
include "mpan2.mm"
include "fvex.mm"
include "elpw.mm"
include "sylibr.mm"
include "ralimi.mm"
include "syl.mm"
include "wb.mm"
include "onss.mm"
include "fndm.mm"
include "syl6sseqr.mm"
include "funimass4.mm"
include "mpbird.mm"
include "sspwuni.mm"
include "sylib.mm"
include "rnss.mm"
include "rnxpss.mm"
include "syl6ss.mm"
include "ssonuni.mm"
include "sylc.mm"
include "suceloni.mm"
include "ad2antrr.mm"
include "rankon.mm"
include "omcl.mm"
include "sylancl.mm"
include "rankr1ai.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "eleqtrd.mm"
include "word.mm"
include "eloni.mm"
include "ordsucuniel.mm"
include "mpbid.mm"
include "fveq2.mm"
include "f1eq1.mm"
include "f1eq2.mm"
include "bitrd.mm"
include "rspcv.mm"
include "r1elwf.mm"
include "rankidb.mm"
include "ffvelrnd.mm"
include "oacl.mm"
include "syl2anc.mm"
include "wn.mm"
include "char.mm"
include "imassrn.mm"
include "wiso.mm"
include "wf1o.mm"
include "wwe.mm"
include "rnex.mm"
include "onuni.mm"
include "sucidg.mm"
include "wo.mm"
include "adantr.mm"
include "orduniorsuc.mm"
include "orcanai.mm"
include "eleqtrrd.mm"
include "frn.mm"
include "epweon.mm"
include "wess.mm"
include "mpisyl.mm"
include "eqid.mm"
include "oiiso.mm"
include "isof1o.mm"
include "f1ocnv.mm"
include "f1of1.mm"
include "4syl.mm"
include "f1f1orn.mm"
include "f1co.mm"
include "harcl.mm"
include "onordi.mm"
include "cdom.mm"
include "wbr.mm"
include "oion.mm"
include "mp1i.mm"
include "cen.mm"
include "oien.mm"
include "f1oen.mm"
include "ensym.mm"
include "sseldd.mm"
include "r1ord2.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "endomtr.mm"
include "elharval.mm"
include "sylanbrc.mm"
include "ordelss.mm"
include "sstrd.mm"
include "syl5ss.mm"
include "elpw2.mm"
include "ifclda.mm"
include "ex.mm"
include "iftrue.mm"
include "eqeq12d.mm"
include "adantl.mm"
include "c0.mm"
include "wne.mm"
include "nsuceq0.mm"
include "a1i.mm"
include "onsucuni.mm"
include "fnfvima.mm"
include "syl3anc.mm"
include "elssuni.mm"
include "f1fn.mm"
include "fnfvelrn.mm"
include "adantlrr.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "anbi1d.mm"
include "suceq.mm"
include "fveq2d.mm"
include "id.mm"
include "fveq12d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvarv.mm"
include "adantlrl.mm"
include "omopth2.mm"
include "syl222anc.mm"
include "fveq1d.mm"
include "eqeq2d.mm"
include "ad2antll.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "bitr3d.mm"
include "biimpd.mm"
include "expimpd.mm"
include "jca.mm"
include "impbid1.mm"
include "3bitrd.mm"
include "iffalse.mm"
include "imaeq2.mm"
include "simplrl.mm"
include "r1suc.mm"
include "eqtrd.mm"
include "elpwid.mm"
include "simplrr.mm"
include "f1imaeq.mm"
include "pm2.61dan.mm"
include "dom2lem.mm"
include "dfac12lem1.mm"

theorem dfac12lem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cC: class C
  let cF: class F
  let cG: class G
  let cH: class H
  let vm: setvar m
  let vn: setvar n
  assume dfac12.1: |- ( ph -> A e. On )
  assume dfac12.3: |- ( ph -> F : ~P ( har ` ( R1 ` A ) ) -1-1-> On )
  assume dfac12.4: |- G = recs ( ( x e. _V |-> ( y e. ( R1 ` dom x ) |-> if ( dom x = U. dom x , ( ( suc U. ran U. ran x .o ( rank ` y ) ) +o ( ( x ` suc ( rank ` y ) ) ` y ) ) , ( F ` ( ( `' OrdIso ( _E , ran ( x ` U. dom x ) ) o. ( x ` U. dom x ) ) " y ) ) ) ) ) )
  assume dfac12.5: |- ( ph -> C e. On )
  assume dfac12.h: |- H = ( `' OrdIso ( _E , ran ( G ` U. C ) ) o. ( G ` U. C ) )
  assume dfac12.6: |- ( ph -> C C_ A )
  assume dfac12.8: |- ( ph -> A. z e. C ( G ` z ) : ( R1 ` z ) -1-1-> On )

  disjoint y z
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint ph y
  disjoint ph z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint H y
  disjoint H z
  disjoint m n
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint m x
  disjoint G m
  disjoint n x
  disjoint G n
  disjoint m ph
  disjoint n ph
  assert |- ( ph -> ( G ` C ) : ( R1 ` C ) -1-1-> On )

  proof
    wph
    cC
    cr1
    cfv
    #
    con0
    cC
    cG
    cfv
    #
    wf1
    #
    @0
    con0
    vy
    @0
    cC
    cC
    cuni
    #
    wceq
    #
    cG
    cC
    cima
    #
    cuni
    #
    crn
    #
    cuni
    #
    csuc
    #
    vy
    cv
    #
    crnk
    cfv
    #
    comu
    co
    #
    @10
    @11
    csuc
    #
    cG
    cfv
    #
    cfv
    #
    coa
    co
    #
    cH
    @10
    cima
    #
    cF
    cfv
    #
    cif
    #
    cmpt
    #
    wf1
    #
    wph
    vy
    vz
    @0
    con0
    @19
    @4
    @9
    vz
    cv
    #
    crnk
    cfv
    #
    comu
    co
    @22
    @23
    csuc
    #
    cG
    cfv
    #
    cfv
    #
    coa
    co
    #
    cH
    @22
    cima
    #
    cF
    cfv
    #
    cif
    #
    wph
    @10
    @0
    wcel
    #
    @19
    con0
    wcel
    wph
    @31
    wa
    #
    @4
    @16
    @18
    con0
    @32
    @4
    wa
    #
    @12
    con0
    wcel
    #
    @15
    con0
    wcel
    @16
    con0
    wcel
    @33
    @9
    con0
    wcel
    #
    @11
    con0
    wcel
    #
    @34
    wph
    @35
    @31
    @4
    wph
    @8
    con0
    wcel
    #
    @35
    wph
    @7
    cvv
    wcel
    #
    @7
    con0
    wss
    #
    @37
    wph
    @5
    cvv
    wcel
    #
    @6
    cvv
    wcel
    @38
    wph
    cG
    wfun
    #
    cC
    con0
    wcel
    #
    @40
    cG
    con0
    wfn
    #
    @41
    cG
    vx
    cvv
    vy
    vx
    cv
    #
    cdm
    #
    cr1
    cfv
    @45
    @45
    cuni
    #
    wceq
    @44
    crn
    cuni
    crn
    cuni
    csuc
    @11
    comu
    co
    @10
    @13
    @44
    cfv
    cfv
    coa
    co
    @46
    @44
    cfv
    #
    crn
    cep
    coi
    ccnv
    @47
    ccom
    @10
    cima
    cF
    cfv
    cif
    cmpt
    cmpt
    dfac12.4
    tfr1
    #
    con0
    cG
    fnfun
    ax-mp
    #
    dfac12.5
    cG
    cC
    con0
    funimaexg
    sylancr
    @5
    cvv
    uniexg
    @6
    cvv
    rnexg
    3syl
    wph
    @7
    cvv
    con0
    cxp
    #
    crn
    #
    con0
    wph
    @6
    @50
    wss
    #
    @7
    @51
    wss
    wph
    @5
    @50
    cpw
    #
    wss
    #
    @52
    wph
    @54
    @22
    cG
    cfv
    #
    @53
    wcel
    #
    vz
    cC
    wral
    #
    wph
    @22
    cr1
    cfv
    #
    con0
    @55
    wf1
    #
    vz
    cC
    wral
    #
    @57
    dfac12.8
    @59
    @56
    vz
    cC
    @59
    @58
    con0
    @55
    wf
    @55
    @58
    con0
    cxp
    #
    wss
    #
    @56
    @58
    con0
    @55
    f1f
    @58
    con0
    @55
    fssxp
    @62
    @55
    @50
    wss
    #
    @56
    @62
    @61
    @50
    wss
    #
    @63
    @58
    cvv
    wss
    @64
    @58
    ssv
    @58
    cvv
    con0
    xpss1
    ax-mp
    @55
    @61
    @50
    sstr
    mpan2
    @55
    @50
    @22
    cG
    fvex
    elpw
    sylibr
    3syl
    ralimi
    syl
    wph
    @41
    cC
    cG
    cdm
    #
    wss
    @54
    @57
    wb
    @49
    wph
    cC
    con0
    @65
    wph
    @42
    cC
    con0
    wss
    #
    dfac12.5
    cC
    onss
    syl
    #
    @43
    @65
    con0
    wceq
    @48
    con0
    cG
    fndm
    ax-mp
    syl6sseqr
    vz
    cC
    @53
    cG
    funimass4
    sylancr
    mpbird
    @5
    @50
    sspwuni
    sylib
    @6
    @50
    rnss
    syl
    cvv
    con0
    rnxpss
    syl6ss
    #
    @7
    cvv
    ssonuni
    sylc
    @8
    suceloni
    syl
    #
    ad2antrr
    @10
    rankon
    #
    @9
    @11
    omcl
    sylancl
    @33
    @13
    cr1
    cfv
    #
    con0
    @10
    @14
    @33
    @71
    con0
    @14
    wf1
    #
    @71
    con0
    @14
    wf
    @33
    @13
    cC
    wcel
    #
    @60
    @72
    @33
    @11
    @3
    wcel
    #
    @73
    @33
    @11
    cC
    @3
    @31
    @11
    cC
    wcel
    wph
    @4
    @10
    cC
    rankr1ai
    ad2antlr
    @32
    @4
    simpr
    eleqtrd
    @33
    cC
    word
    #
    @74
    @73
    wb
    wph
    @75
    @31
    @4
    wph
    @42
    @75
    dfac12.5
    cC
    eloni
    syl
    #
    ad2antrr
    @11
    cC
    ordsucuniel
    syl
    mpbid
    #
    wph
    @60
    @31
    @4
    dfac12.8
    ad2antrr
    @59
    @72
    vz
    @13
    cC
    @22
    @13
    wceq
    #
    @59
    @58
    con0
    @14
    wf1
    #
    @72
    @78
    @55
    @14
    wceq
    @59
    @79
    wb
    @22
    @13
    cG
    fveq2
    @58
    con0
    @55
    @14
    f1eq1
    syl
    @78
    @58
    @71
    wceq
    @79
    @72
    wb
    @22
    @13
    cr1
    fveq2
    @58
    @71
    con0
    @14
    f1eq2
    syl
    bitrd
    rspcv
    sylc
    #
    @71
    con0
    @14
    f1f
    syl
    @33
    @10
    cr1
    con0
    cima
    cuni
    #
    wcel
    #
    @10
    @71
    wcel
    #
    @31
    @82
    wph
    @4
    @10
    cC
    r1elwf
    ad2antlr
    @10
    rankidb
    syl
    #
    ffvelrnd
    @12
    @15
    oacl
    syl2anc
    @32
    @4
    wn
    #
    wa
    #
    cA
    cr1
    cfv
    #
    char
    cfv
    #
    cpw
    #
    con0
    @17
    cF
    wph
    @89
    con0
    cF
    wf
    #
    @31
    @85
    wph
    @89
    con0
    cF
    wf1
    #
    @90
    dfac12.3
    @89
    con0
    cF
    f1f
    syl
    ad2antrr
    @86
    @17
    @88
    wss
    @17
    @89
    wcel
    #
    @86
    @17
    cH
    crn
    #
    @88
    cH
    @10
    imassrn
    @86
    @93
    @3
    cG
    cfv
    #
    crn
    #
    cep
    coi
    #
    cdm
    #
    @88
    @86
    @3
    cr1
    cfv
    #
    @97
    cH
    wf1
    #
    @98
    @97
    cH
    wf
    @93
    @97
    wss
    @86
    @98
    @97
    @96
    ccnv
    #
    @94
    ccom
    #
    wf1
    #
    @99
    @86
    @95
    @97
    @100
    wf1
    #
    @98
    @95
    @94
    wf1
    #
    @102
    @86
    @97
    @95
    cep
    cep
    @96
    wiso
    #
    @97
    @95
    @96
    wf1o
    @95
    @97
    @100
    wf1o
    @103
    @86
    @95
    cvv
    wcel
    #
    @95
    cep
    wwe
    #
    @105
    @94
    @3
    cG
    fvex
    rnex
    #
    @86
    @95
    con0
    wss
    #
    con0
    cep
    wwe
    @107
    @86
    @98
    con0
    @94
    wf1
    #
    @98
    con0
    @94
    wf
    @109
    @86
    @3
    cC
    wcel
    @60
    @110
    @86
    @3
    @3
    csuc
    #
    cC
    @86
    @42
    @3
    con0
    wcel
    #
    @3
    @111
    wcel
    wph
    @42
    @31
    @85
    dfac12.5
    ad2antrr
    #
    cC
    onuni
    #
    @3
    con0
    sucidg
    3syl
    @32
    @4
    cC
    @111
    wceq
    #
    @32
    @75
    @4
    @115
    wo
    wph
    @75
    @31
    @76
    adantr
    cC
    orduniorsuc
    syl
    orcanai
    #
    eleqtrrd
    #
    wph
    @60
    @31
    @85
    dfac12.8
    ad2antrr
    @59
    @110
    vz
    @3
    cC
    @22
    @3
    wceq
    #
    @59
    @58
    con0
    @94
    wf1
    #
    @110
    @118
    @55
    @94
    wceq
    @59
    @119
    wb
    @22
    @3
    cG
    fveq2
    @58
    con0
    @55
    @94
    f1eq1
    syl
    @118
    @58
    @98
    wceq
    @119
    @110
    wb
    @22
    @3
    cr1
    fveq2
    @58
    @98
    con0
    @94
    f1eq2
    syl
    bitrd
    rspcv
    sylc
    #
    @98
    con0
    @94
    f1f
    @98
    con0
    @94
    frn
    3syl
    epweon
    @95
    con0
    cep
    wess
    mpisyl
    #
    @95
    cep
    @96
    cvv
    @96
    eqid
    #
    oiiso
    sylancr
    @97
    @95
    cep
    cep
    @96
    isof1o
    @97
    @95
    @96
    f1ocnv
    @95
    @97
    @100
    f1of1
    4syl
    @86
    @110
    @98
    @95
    @94
    wf1o
    #
    @104
    @120
    @98
    con0
    @94
    f1f1orn
    #
    @98
    @95
    @94
    f1of1
    3syl
    @98
    @95
    @97
    @100
    @94
    f1co
    syl2anc
    cH
    @101
    wceq
    @99
    @102
    wb
    dfac12.h
    @98
    @97
    cH
    @101
    f1eq1
    ax-mp
    sylibr
    #
    @98
    @97
    cH
    f1f
    @98
    @97
    cH
    frn
    3syl
    @86
    @88
    word
    @97
    @88
    wcel
    #
    @97
    @88
    wss
    @88
    @87
    harcl
    onordi
    @86
    @97
    con0
    wcel
    #
    @97
    @87
    cdom
    wbr
    #
    @126
    @106
    @127
    @86
    @108
    @95
    cep
    @96
    cvv
    @122
    oion
    mp1i
    @86
    @97
    @95
    cen
    wbr
    #
    @95
    @87
    cdom
    wbr
    #
    @128
    @86
    @106
    @107
    @129
    @108
    @121
    @95
    cep
    @96
    cvv
    @122
    oien
    sylancr
    @86
    @95
    @98
    cen
    wbr
    #
    @98
    @87
    cdom
    wbr
    #
    @130
    @86
    @110
    @123
    @98
    @95
    cen
    wbr
    @131
    @120
    @124
    @98
    @95
    @94
    @3
    cr1
    fvex
    f1oen
    @98
    @95
    ensym
    4syl
    @87
    cvv
    wcel
    @86
    @98
    @87
    wss
    #
    @132
    cA
    cr1
    fvex
    @86
    cA
    con0
    wcel
    #
    @3
    cA
    wcel
    @133
    wph
    @134
    @31
    @85
    dfac12.1
    ad2antrr
    @86
    cC
    cA
    @3
    wph
    cC
    cA
    wss
    @31
    @85
    dfac12.6
    ad2antrr
    @117
    sseldd
    @3
    cA
    r1ord2
    sylc
    @98
    @87
    cvv
    ssdomg
    mpsyl
    @95
    @98
    @87
    endomtr
    syl2anc
    @97
    @95
    @87
    endomtr
    syl2anc
    @87
    @97
    elharval
    sylanbrc
    @88
    @97
    ordelss
    sylancr
    sstrd
    syl5ss
    @17
    @88
    @87
    char
    fvex
    elpw2
    sylibr
    #
    ffvelrnd
    ifclda
    ex
    wph
    @31
    @22
    @0
    wcel
    #
    wa
    #
    @19
    @30
    wceq
    #
    @10
    @22
    wceq
    #
    wb
    #
    wph
    @137
    wa
    #
    @4
    @140
    @141
    @4
    wa
    #
    @138
    @16
    @27
    wceq
    #
    @11
    @23
    wceq
    #
    @15
    @26
    wceq
    #
    wa
    #
    @139
    @4
    @138
    @143
    wb
    @141
    @4
    @19
    @16
    @30
    @27
    @4
    @16
    @18
    iftrue
    @4
    @27
    @29
    iftrue
    eqeq12d
    adantl
    @142
    @35
    @9
    c0
    wne
    #
    @36
    @15
    @9
    wcel
    #
    @23
    con0
    wcel
    #
    @26
    @9
    wcel
    #
    @143
    @146
    wb
    wph
    @35
    @137
    @4
    @69
    ad2antrr
    @147
    @142
    @8
    nsuceq0
    a1i
    @36
    @142
    @70
    a1i
    wph
    @31
    @4
    @148
    @136
    @33
    @7
    @9
    @15
    wph
    @7
    @9
    wss
    #
    @31
    @4
    wph
    @39
    @151
    @68
    @7
    onsucuni
    syl
    ad2antrr
    @33
    @14
    crn
    #
    @7
    @15
    @33
    @14
    @5
    wcel
    #
    @14
    @6
    wss
    @152
    @7
    wss
    @33
    @43
    @66
    @73
    @153
    @43
    @33
    @48
    a1i
    wph
    @66
    @31
    @4
    @67
    ad2antrr
    @77
    con0
    cC
    cG
    @13
    fnfvima
    syl3anc
    @14
    @5
    elssuni
    @14
    @6
    rnss
    3syl
    @33
    @14
    @71
    wfn
    #
    @83
    @15
    @152
    wcel
    @33
    @72
    @154
    @80
    @71
    con0
    @14
    f1fn
    syl
    @84
    @71
    @10
    @14
    fnfvelrn
    syl2anc
    sseldd
    sseldd
    #
    adantlrr
    @149
    @142
    @22
    rankon
    a1i
    wph
    @136
    @4
    @150
    @31
    @33
    @148
    wi
    wph
    @136
    wa
    #
    @4
    wa
    #
    @150
    wi
    vy
    vz
    @139
    @33
    @157
    @148
    @150
    @139
    @32
    @156
    @4
    @139
    @31
    @136
    wph
    @10
    @22
    @0
    eleq1
    anbi2d
    #
    anbi1d
    @139
    @15
    @26
    @9
    @139
    @10
    @22
    @14
    @25
    @139
    @13
    @24
    cG
    @139
    @144
    @13
    @24
    wceq
    #
    @10
    @22
    crnk
    fveq2
    #
    @11
    @23
    suceq
    #
    syl
    fveq2d
    @139
    id
    fveq12d
    #
    eleq1d
    imbi12d
    @155
    chvarv
    adantlrl
    @9
    @11
    @15
    @23
    @26
    omopth2
    syl222anc
    @142
    @146
    @139
    @142
    @144
    @145
    @139
    @142
    @144
    wa
    #
    @145
    @139
    @163
    @15
    @22
    @14
    cfv
    #
    wceq
    #
    @145
    @139
    @163
    @164
    @26
    @15
    @163
    @22
    @14
    @25
    @163
    @13
    @24
    cG
    @144
    @159
    @142
    @161
    adantl
    #
    fveq2d
    fveq1d
    eqeq2d
    @163
    @72
    @83
    @22
    @71
    wcel
    @165
    @139
    wb
    @142
    @72
    @144
    wph
    @31
    @4
    @72
    @136
    @80
    adantlrr
    adantr
    @142
    @83
    @144
    wph
    @31
    @4
    @83
    @136
    @84
    adantlrr
    adantr
    @163
    @22
    @24
    cr1
    cfv
    #
    @71
    @141
    @22
    @167
    wcel
    #
    @4
    @144
    @136
    @168
    wph
    @31
    @136
    @22
    @81
    wcel
    @168
    @22
    cC
    r1elwf
    @22
    rankidb
    syl
    ad2antll
    ad2antrr
    @163
    @13
    @24
    cr1
    @166
    fveq2d
    eleqtrrd
    @71
    con0
    @10
    @22
    @14
    f1fveq
    syl12anc
    bitr3d
    biimpd
    expimpd
    @139
    @144
    @145
    @160
    @162
    jca
    impbid1
    3bitrd
    @141
    @85
    wa
    #
    @138
    @18
    @29
    wceq
    #
    @17
    @28
    wceq
    #
    @139
    @85
    @138
    @170
    wb
    @141
    @85
    @19
    @18
    @30
    @29
    @4
    @16
    @18
    iffalse
    @4
    @27
    @29
    iffalse
    eqeq12d
    adantl
    @169
    @91
    @92
    @28
    @89
    wcel
    #
    @170
    @171
    wb
    wph
    @91
    @137
    @85
    dfac12.3
    ad2antrr
    wph
    @31
    @85
    @92
    @136
    @135
    adantlrr
    wph
    @136
    @85
    @172
    @31
    @86
    @92
    wi
    @156
    @85
    wa
    #
    @172
    wi
    vy
    vz
    @139
    @86
    @173
    @92
    @172
    @139
    @32
    @156
    @85
    @158
    anbi1d
    @139
    @17
    @28
    @89
    @10
    @22
    cH
    imaeq2
    eleq1d
    imbi12d
    @135
    chvarv
    adantlrl
    @89
    con0
    @17
    @28
    cF
    f1fveq
    syl12anc
    @169
    @99
    @10
    @98
    wss
    @22
    @98
    wss
    @171
    @139
    wb
    wph
    @31
    @85
    @99
    @136
    @125
    adantlrr
    @169
    @10
    @98
    @169
    @10
    @0
    @98
    cpw
    #
    wph
    @31
    @136
    @85
    simplrl
    wph
    @31
    @85
    @0
    @174
    wceq
    @136
    @86
    @0
    @111
    cr1
    cfv
    #
    @174
    @86
    cC
    @111
    cr1
    @116
    fveq2d
    @86
    @42
    @112
    @175
    @174
    wceq
    @113
    @114
    @3
    r1suc
    3syl
    eqtrd
    adantlrr
    #
    eleqtrd
    elpwid
    @169
    @22
    @98
    @169
    @22
    @0
    @174
    wph
    @31
    @136
    @85
    simplrr
    @176
    eleqtrd
    elpwid
    @98
    @97
    @10
    @22
    cH
    f1imaeq
    syl12anc
    3bitrd
    pm2.61dan
    ex
    dom2lem
    wph
    @1
    @20
    wceq
    @2
    @21
    wb
    wph
    vx
    vy
    cA
    cC
    cF
    cG
    cH
    dfac12.1
    dfac12.3
    dfac12.4
    dfac12.5
    dfac12.h
    dfac12lem1
    @0
    con0
    @1
    @20
    f1eq1
    syl
    mpbird
end
