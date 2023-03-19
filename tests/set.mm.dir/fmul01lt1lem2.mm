include "wceq.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "nfv.mm"
include "nfan.mm"
include "cz.mm"
include "wcel.mm"
include "adantr.mm"
include "cuz.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "cr.mm"
include "adantlr.mm"
include "cc0.mm"
include "cle.mm"
include "c1.mm"
include "crp.mm"
include "simpr.mm"
include "fveq2d.mm"
include "eqbrtrrd.mm"
include "fmul01lt1lem1.mm"
include "wn.mm"
include "cmul.mm"
include "cseq.mm"
include "fveq1i.mm"
include "wi.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfel1.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "remulcl.mm"
include "adantl.mm"
include "seqcl.mm"
include "elfzuz3.mm"
include "syl.mm"
include "w3a.mm"
include "eluzelz.mm"
include "elfzelz.mm"
include "3jca.mm"
include "zred.mm"
include "elfzle1.mm"
include "letrd.mm"
include "elfzle2.mm"
include "jca.mm"
include "elfz2.mm"
include "sylanbrc.mm"
include "syldan.mm"
include "rpred.mm"
include "cmin.mm"
include "caddc.mm"
include "simp1.mm"
include "recnd.mm"
include "simp2.mm"
include "simp3.mm"
include "mulassd.mm"
include "zcnd.mm"
include "1cnd.mm"
include "npcand.mm"
include "eleqtrrd.mm"
include "1zzd.mm"
include "zsubcld.mm"
include "wo.mm"
include "eqcom.mm"
include "sylnib.mm"
include "leloed.mm"
include "mpbid.mm"
include "orel2.mm"
include "sylc.mm"
include "wb.mm"
include "zltlem1.mm"
include "syl2anc.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "seqsplit.mm"
include "seqeq1d.mm"
include "fveq1d.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "1red.mm"
include "resubcld.mm"
include "lem1d.mm"
include "eqid.mm"
include "eluzfz2.mm"
include "fmul01.mm"
include "simpld.mm"
include "letr.mm"
include "simprd.mm"
include "lemul1ad.mm"
include "eqbrtrd.mm"
include "mulid2d.mm"
include "breqtrd.mm"
include "lelttrd.mm"
include "syl5eqbr.mm"
include "pm2.61dan.mm"

theorem fmul01lt1lem2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vi: setvar i
  let cE: class E
  let cJ: class J
  let cL: class L
  let cM: class M
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vj: setvar j
  assume fmul01lt1lem2.1: |- F/_ i B
  assume fmul01lt1lem2.2: |- F/ i ph
  assume fmul01lt1lem2.3: |- A = seq L ( x. , B )
  assume fmul01lt1lem2.4: |- ( ph -> L e. ZZ )
  assume fmul01lt1lem2.5: |- ( ph -> M e. ( ZZ>= ` L ) )
  assume fmul01lt1lem2.6: |- ( ( ph /\ i e. ( L ... M ) ) -> ( B ` i ) e. RR )
  assume fmul01lt1lem2.7: |- ( ( ph /\ i e. ( L ... M ) ) -> 0 <_ ( B ` i ) )
  assume fmul01lt1lem2.8: |- ( ( ph /\ i e. ( L ... M ) ) -> ( B ` i ) <_ 1 )
  assume fmul01lt1lem2.9: |- ( ph -> E e. RR+ )
  assume fmul01lt1lem2.10: |- ( ph -> J e. ( L ... M ) )
  assume fmul01lt1lem2.11: |- ( ph -> ( B ` J ) < E )

  disjoint J i
  disjoint L i
  disjoint M i
  disjoint a b
  disjoint a c
  disjoint B a
  disjoint b c
  disjoint B b
  disjoint B c
  disjoint a i
  disjoint J a
  disjoint a j
  disjoint B j
  disjoint L a
  disjoint L b
  disjoint L c
  disjoint M a
  disjoint M b
  disjoint M c
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint J b
  disjoint J c
  disjoint J j
  disjoint L j
  disjoint j ph
  assert |- ( ph -> ( A ` M ) < E )

  proof
    wph
    cJ
    cL
    wceq
    #
    cM
    cA
    cfv
    #
    cE
    clt
    wbr
    wph
    @0
    wa
    #
    cA
    cB
    vi
    cE
    cL
    cM
    fmul01lt1lem2.1
    wph
    @0
    vi
    fmul01lt1lem2.2
    @0
    vi
    nfv
    nfan
    fmul01lt1lem2.3
    wph
    cL
    cz
    wcel
    #
    @0
    fmul01lt1lem2.4
    adantr
    wph
    cM
    cL
    cuz
    cfv
    #
    wcel
    #
    @0
    fmul01lt1lem2.5
    adantr
    wph
    vi
    cv
    #
    cL
    cM
    cfz
    co
    #
    wcel
    #
    @6
    cB
    cfv
    #
    cr
    wcel
    #
    @0
    fmul01lt1lem2.6
    adantlr
    wph
    @8
    cc0
    @9
    cle
    wbr
    #
    @0
    fmul01lt1lem2.7
    adantlr
    wph
    @8
    @9
    c1
    cle
    wbr
    #
    @0
    fmul01lt1lem2.8
    adantlr
    wph
    cE
    crp
    wcel
    @0
    fmul01lt1lem2.9
    adantr
    @2
    cJ
    cB
    cfv
    #
    cL
    cB
    cfv
    cE
    clt
    @2
    cJ
    cL
    cB
    wph
    @0
    simpr
    fveq2d
    wph
    @13
    cE
    clt
    wbr
    @0
    fmul01lt1lem2.11
    adantr
    eqbrtrrd
    fmul01lt1lem1
    wph
    @0
    wn
    #
    wa
    #
    @1
    cM
    cmul
    cB
    cL
    cseq
    #
    cfv
    #
    cE
    clt
    cM
    cA
    @16
    fmul01lt1lem2.3
    fveq1i
    @15
    @17
    cM
    cmul
    cB
    cJ
    cseq
    #
    cfv
    #
    cE
    wph
    @17
    cr
    wcel
    @14
    wph
    va
    vj
    cmul
    cr
    cB
    cL
    cM
    fmul01lt1lem2.5
    wph
    @8
    wa
    #
    @10
    wi
    wph
    va
    cv
    #
    @7
    wcel
    #
    wa
    #
    @21
    cB
    cfv
    #
    cr
    wcel
    #
    wi
    vi
    va
    @23
    @25
    vi
    wph
    @22
    vi
    fmul01lt1lem2.2
    @22
    vi
    nfv
    #
    nfan
    vi
    @24
    cr
    vi
    @21
    cB
    fmul01lt1lem2.1
    vi
    @21
    nfcv
    nffv
    nfel1
    #
    nfim
    @6
    @21
    wceq
    #
    @20
    @23
    @10
    @25
    @28
    @8
    @22
    wph
    @6
    @21
    @7
    eleq1
    #
    anbi2d
    @28
    @9
    @24
    cr
    @6
    @21
    cB
    fveq2
    eleq1d
    #
    imbi12d
    fmul01lt1lem2.6
    chvar
    @21
    cr
    wcel
    #
    vj
    cv
    #
    cr
    wcel
    wa
    #
    @21
    @32
    cmul
    co
    cr
    wcel
    #
    wph
    @21
    @32
    remulcl
    #
    adantl
    #
    seqcl
    adantr
    wph
    @19
    cr
    wcel
    @14
    wph
    va
    vj
    cmul
    cr
    cB
    cJ
    cM
    wph
    cJ
    @7
    wcel
    #
    cM
    cJ
    cuz
    cfv
    #
    wcel
    #
    fmul01lt1lem2.10
    cJ
    cL
    cM
    elfzuz3
    syl
    #
    wph
    @6
    cJ
    cM
    cfz
    co
    #
    wcel
    #
    wa
    #
    @10
    wi
    wph
    @21
    @41
    wcel
    #
    wa
    #
    @25
    wi
    vi
    va
    @45
    @25
    vi
    wph
    @44
    vi
    fmul01lt1lem2.2
    @44
    vi
    nfv
    nfan
    @27
    nfim
    @28
    @43
    @45
    @10
    @25
    @28
    @42
    @44
    wph
    @6
    @21
    @41
    eleq1
    anbi2d
    @30
    imbi12d
    wph
    @42
    @8
    @10
    @43
    @3
    cM
    cz
    wcel
    #
    @6
    cz
    wcel
    #
    w3a
    #
    cL
    @6
    cle
    wbr
    #
    @6
    cM
    cle
    wbr
    #
    wa
    #
    @8
    @43
    @3
    @46
    @47
    wph
    @3
    @42
    fmul01lt1lem2.4
    adantr
    wph
    @46
    @42
    wph
    @5
    @46
    fmul01lt1lem2.5
    cL
    cM
    eluzelz
    syl
    #
    adantr
    @42
    @47
    wph
    @6
    cJ
    cM
    elfzelz
    #
    adantl
    3jca
    @43
    @49
    @50
    @43
    cL
    cJ
    @6
    wph
    cL
    cr
    wcel
    @42
    wph
    cL
    fmul01lt1lem2.4
    zred
    #
    adantr
    wph
    cJ
    cr
    wcel
    #
    @42
    wph
    cJ
    wph
    @37
    cJ
    cz
    wcel
    #
    fmul01lt1lem2.10
    cJ
    cL
    cM
    elfzelz
    syl
    #
    zred
    #
    adantr
    @42
    @6
    cr
    wcel
    #
    wph
    @42
    @6
    @53
    zred
    adantl
    wph
    cL
    cJ
    cle
    wbr
    #
    @42
    wph
    @37
    @60
    fmul01lt1lem2.10
    cJ
    cL
    cM
    elfzle1
    syl
    #
    adantr
    @42
    cJ
    @6
    cle
    wbr
    wph
    @6
    cJ
    cM
    elfzle1
    adantl
    letrd
    @42
    @50
    wph
    @6
    cJ
    cM
    elfzle2
    adantl
    jca
    @6
    cL
    cM
    elfz2
    #
    sylanbrc
    #
    fmul01lt1lem2.6
    syldan
    #
    chvar
    @36
    seqcl
    adantr
    #
    wph
    cE
    cr
    wcel
    @14
    wph
    cE
    fmul01lt1lem2.9
    rpred
    adantr
    @15
    @17
    c1
    @19
    cmul
    co
    #
    @19
    cle
    @15
    @17
    cJ
    c1
    cmin
    co
    #
    @16
    cfv
    #
    @19
    cmul
    co
    #
    @66
    cle
    @15
    @17
    @68
    cM
    cmul
    cB
    @67
    c1
    caddc
    co
    #
    cseq
    #
    cfv
    #
    cmul
    co
    @69
    @15
    va
    vb
    vc
    cmul
    cr
    cB
    cL
    @67
    cM
    @31
    vb
    cv
    #
    cr
    wcel
    #
    wa
    @21
    @73
    cmul
    co
    #
    cr
    wcel
    @15
    @21
    @73
    remulcl
    adantl
    @31
    @74
    vc
    cv
    #
    cr
    wcel
    #
    w3a
    #
    @75
    @76
    cmul
    co
    @21
    @73
    @76
    cmul
    co
    cmul
    co
    wceq
    @15
    @78
    @21
    @73
    @76
    @78
    @21
    @31
    @74
    @77
    simp1
    recnd
    @78
    @73
    @31
    @74
    @77
    simp2
    recnd
    @78
    @76
    @31
    @74
    @77
    simp3
    recnd
    mulassd
    adantl
    wph
    cM
    @70
    cuz
    cfv
    #
    wcel
    @14
    wph
    cM
    @38
    @79
    @40
    wph
    @70
    cJ
    cuz
    wph
    cJ
    c1
    wph
    cJ
    @57
    zcnd
    wph
    1cnd
    npcand
    #
    fveq2d
    eleqtrrd
    adantr
    @15
    @3
    @67
    cz
    wcel
    #
    cL
    @67
    cle
    wbr
    #
    @67
    @4
    wcel
    wph
    @3
    @14
    fmul01lt1lem2.4
    adantr
    #
    @15
    cJ
    c1
    wph
    @56
    @14
    @57
    adantr
    #
    @15
    1zzd
    zsubcld
    @15
    cL
    cJ
    clt
    wbr
    #
    @82
    @15
    cL
    cJ
    wceq
    #
    wn
    @85
    @86
    wo
    #
    @85
    @15
    @0
    @86
    wph
    @14
    simpr
    cJ
    cL
    eqcom
    sylnib
    wph
    @87
    @14
    wph
    @60
    @87
    @61
    wph
    cL
    cJ
    @54
    @58
    leloed
    mpbid
    adantr
    @86
    @85
    orel2
    sylc
    wph
    @85
    @82
    wb
    #
    @14
    wph
    @3
    @56
    @88
    fmul01lt1lem2.4
    @57
    cL
    cJ
    zltlem1
    syl2anc
    adantr
    mpbid
    #
    cL
    @67
    eluz2
    syl3anbrc
    #
    @15
    @8
    wa
    #
    @10
    wi
    @15
    @22
    wa
    #
    @25
    wi
    vi
    va
    @92
    @25
    vi
    @15
    @22
    vi
    wph
    @14
    vi
    fmul01lt1lem2.2
    @14
    vi
    nfv
    nfan
    #
    @26
    nfan
    @27
    nfim
    @28
    @91
    @92
    @10
    @25
    @28
    @8
    @22
    @15
    @29
    anbi2d
    @30
    imbi12d
    wph
    @8
    @10
    @14
    fmul01lt1lem2.6
    adantlr
    #
    chvar
    seqsplit
    @15
    @72
    @19
    @68
    cmul
    @15
    cM
    @71
    @18
    @15
    @70
    cJ
    cmul
    cB
    wph
    @70
    cJ
    wceq
    @14
    @80
    adantr
    seqeq1d
    fveq1d
    oveq2d
    eqtrd
    @15
    @68
    c1
    @19
    @15
    va
    vj
    cmul
    cr
    cB
    cL
    @67
    @90
    @15
    @6
    cL
    @67
    cfz
    co
    #
    wcel
    #
    wa
    #
    @10
    wi
    @15
    @21
    @95
    wcel
    #
    wa
    #
    @25
    wi
    vi
    va
    @99
    @25
    vi
    @15
    @98
    vi
    @93
    @98
    vi
    nfv
    nfan
    @27
    nfim
    @28
    @97
    @99
    @10
    @25
    @28
    @96
    @98
    @15
    @6
    @21
    @95
    eleq1
    anbi2d
    @30
    imbi12d
    wph
    @96
    @10
    @14
    wph
    @96
    @8
    @10
    wph
    @96
    wa
    #
    @48
    @51
    @8
    @100
    @3
    @46
    @47
    wph
    @3
    @96
    fmul01lt1lem2.4
    adantr
    wph
    @46
    @96
    @52
    adantr
    @96
    @47
    wph
    @6
    cL
    @67
    elfzelz
    #
    adantl
    3jca
    @100
    @49
    @50
    @96
    @49
    wph
    @6
    cL
    @67
    elfzle1
    adantl
    @100
    @6
    cJ
    cM
    @96
    @59
    wph
    @96
    @6
    @101
    zred
    adantl
    #
    wph
    @55
    @96
    @58
    adantr
    #
    wph
    cM
    cr
    wcel
    #
    @96
    wph
    cM
    @52
    zred
    #
    adantr
    @100
    @6
    @67
    cJ
    @102
    wph
    @67
    cr
    wcel
    #
    @96
    wph
    cJ
    c1
    @58
    wph
    1red
    resubcld
    #
    adantr
    @103
    @96
    @6
    @67
    cle
    wbr
    wph
    @6
    cL
    @67
    elfzle2
    adantl
    wph
    @67
    cJ
    cle
    wbr
    #
    @96
    wph
    cJ
    @58
    lem1d
    adantr
    letrd
    wph
    cJ
    cM
    cle
    wbr
    #
    @96
    wph
    @37
    @109
    fmul01lt1lem2.10
    cJ
    cL
    cM
    elfzle2
    syl
    #
    adantr
    letrd
    jca
    @62
    sylanbrc
    fmul01lt1lem2.6
    syldan
    adantlr
    chvar
    @33
    @34
    @15
    @35
    adantl
    seqcl
    @15
    1red
    @65
    @15
    cc0
    @19
    cle
    wbr
    @19
    c1
    cle
    wbr
    @15
    @18
    cB
    vi
    cM
    cJ
    cM
    fmul01lt1lem2.1
    @93
    @18
    eqid
    #
    @84
    wph
    @39
    @14
    @40
    adantr
    wph
    cM
    @41
    wcel
    #
    @14
    wph
    @39
    @112
    @40
    cJ
    cM
    eluzfz2
    syl
    adantr
    wph
    @42
    @10
    @14
    @64
    adantlr
    wph
    @42
    @11
    @14
    wph
    @42
    @8
    @11
    @63
    fmul01lt1lem2.7
    syldan
    #
    adantlr
    wph
    @42
    @12
    @14
    wph
    @42
    @8
    @12
    @63
    fmul01lt1lem2.8
    syldan
    #
    adantlr
    fmul01
    simpld
    @15
    cc0
    @68
    cle
    wbr
    @68
    c1
    cle
    wbr
    @15
    @16
    cB
    vi
    @67
    cL
    cM
    fmul01lt1lem2.1
    @93
    @16
    eqid
    @83
    wph
    @5
    @14
    fmul01lt1lem2.5
    adantr
    @15
    @3
    @46
    @81
    w3a
    #
    @82
    @67
    cM
    cle
    wbr
    #
    wa
    @67
    @7
    wcel
    wph
    @115
    @14
    wph
    @3
    @46
    @81
    fmul01lt1lem2.4
    @52
    wph
    cJ
    c1
    @57
    wph
    1zzd
    zsubcld
    3jca
    adantr
    @15
    @82
    @116
    @89
    @15
    @106
    @55
    @104
    w3a
    #
    @108
    @109
    wa
    @116
    wph
    @117
    @14
    wph
    @106
    @55
    @104
    @107
    @58
    @105
    3jca
    adantr
    @15
    @108
    @109
    @15
    cJ
    wph
    @55
    @14
    @58
    adantr
    lem1d
    wph
    @109
    @14
    @110
    adantr
    jca
    @67
    cJ
    cM
    letr
    sylc
    jca
    @67
    cL
    cM
    elfz2
    sylanbrc
    @94
    wph
    @8
    @11
    @14
    fmul01lt1lem2.7
    adantlr
    wph
    @8
    @12
    @14
    fmul01lt1lem2.8
    adantlr
    fmul01
    simprd
    lemul1ad
    eqbrtrd
    @15
    @19
    @15
    @19
    @65
    recnd
    mulid2d
    breqtrd
    wph
    @19
    cE
    clt
    wbr
    @14
    wph
    @18
    cB
    vi
    cE
    cJ
    cM
    fmul01lt1lem2.1
    fmul01lt1lem2.2
    @111
    @57
    @40
    @64
    @113
    @114
    fmul01lt1lem2.9
    fmul01lt1lem2.11
    fmul01lt1lem1
    adantr
    lelttrd
    syl5eqbr
    pm2.61dan
end
