include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cc0.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "caddc.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "imbi2d.mm"
include "cuz.mm"
include "zred.mm"
include "leidd.mm"
include "cz.mm"
include "wb.mm"
include "eluzelz.mm"
include "syl.mm"
include "eluz.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "elfz.mm"
include "syl3anc.mm"
include "mpbir2and.mm"
include "ancli.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "imbi12d.mm"
include "vtoclg1f.mm"
include "sylc.mm"
include "cmul.mm"
include "cseq.mm"
include "fveq1i.mm"
include "seq1.mm"
include "syl5eq.mm"
include "breqtrrd.mm"
include "eqbrtrd.mm"
include "jca.mm"
include "a1i.mm"
include "cfzo.mm"
include "w3a.mm"
include "cr.mm"
include "elfzouz.mm"
include "3ad2ant1.mm"
include "simpl3.mm"
include "wss.mm"
include "elfzouz2.mm"
include "fzss2.mm"
include "sselda.mm"
include "nfel1.mm"
include "eleq1d.mm"
include "chvar.mm"
include "remulcl.mm"
include "adantl.mm"
include "seqcl.mm"
include "simp3.mm"
include "fzofzp1.mm"
include "anabsi7.mm"
include "pm3.35.mm"
include "ancoms.mm"
include "simpl.mm"
include "3adant1.mm"
include "syl6breq.mm"
include "simp1.mm"
include "mulge0d.mm"
include "seqp1.mm"
include "syl6breqr.mm"
include "remulcld.mm"
include "1red.mm"
include "lemul2ad.mm"
include "recnd.mm"
include "mulid1d.mm"
include "breqtrd.mm"
include "simp2.mm"
include "simprd.mm"
include "syl5eqbrr.mm"
include "letrd.mm"
include "syl5eqbr.mm"
include "3exp.mm"
include "fzind2.mm"
include "mpcom.mm"

theorem fmul01
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vi: setvar i
  let cK: class K
  let cL: class L
  let cM: class M
  let vj: setvar j
  let vk: setvar k
  let vl: setvar l
  assume fmul01.1: |- F/_ i B
  assume fmul01.2: |- F/ i ph
  assume fmul01.3: |- A = seq L ( x. , B )
  assume fmul01.4: |- ( ph -> L e. ZZ )
  assume fmul01.5: |- ( ph -> M e. ( ZZ>= ` L ) )
  assume fmul01.6: |- ( ph -> K e. ( L ... M ) )
  assume fmul01.7: |- ( ( ph /\ i e. ( L ... M ) ) -> ( B ` i ) e. RR )
  assume fmul01.8: |- ( ( ph /\ i e. ( L ... M ) ) -> 0 <_ ( B ` i ) )
  assume fmul01.9: |- ( ( ph /\ i e. ( L ... M ) ) -> ( B ` i ) <_ 1 )

  disjoint L i
  disjoint M i
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint L j
  disjoint L k
  disjoint M j
  disjoint M k
  disjoint j l
  disjoint A j
  disjoint k l
  disjoint A k
  disjoint A l
  disjoint j ph
  disjoint k ph
  disjoint l ph
  disjoint B k
  disjoint B l
  disjoint K k
  disjoint L l
  disjoint M l
  assert |- ( ph -> ( 0 <_ ( A ` K ) /\ ( A ` K ) <_ 1 ) )

  proof
    cK
    cL
    cM
    cfz
    co
    #
    wcel
    wph
    cc0
    cK
    cA
    cfv
    #
    cle
    wbr
    #
    @1
    c1
    cle
    wbr
    #
    wa
    #
    fmul01.6
    wph
    cc0
    vk
    cv
    #
    cA
    cfv
    #
    cle
    wbr
    #
    @6
    c1
    cle
    wbr
    #
    wa
    #
    wi
    wph
    cc0
    cL
    cA
    cfv
    #
    cle
    wbr
    #
    @10
    c1
    cle
    wbr
    #
    wa
    #
    wi
    #
    wph
    cc0
    vj
    cv
    #
    cA
    cfv
    #
    cle
    wbr
    #
    @16
    c1
    cle
    wbr
    #
    wa
    #
    wi
    #
    wph
    cc0
    @15
    c1
    caddc
    co
    #
    cA
    cfv
    #
    cle
    wbr
    #
    @22
    c1
    cle
    wbr
    #
    wa
    #
    wi
    wph
    @4
    wi
    vk
    vj
    cK
    cL
    cM
    @5
    cL
    wceq
    #
    @9
    @13
    wph
    @26
    @7
    @11
    @8
    @12
    @26
    @6
    @10
    cc0
    cle
    @5
    cL
    cA
    fveq2
    #
    breq2d
    @26
    @6
    @10
    c1
    cle
    @27
    breq1d
    anbi12d
    imbi2d
    @5
    @15
    wceq
    #
    @9
    @19
    wph
    @28
    @7
    @17
    @8
    @18
    @28
    @6
    @16
    cc0
    cle
    @5
    @15
    cA
    fveq2
    #
    breq2d
    @28
    @6
    @16
    c1
    cle
    @29
    breq1d
    anbi12d
    imbi2d
    @5
    @21
    wceq
    #
    @9
    @25
    wph
    @30
    @7
    @23
    @8
    @24
    @30
    @6
    @22
    cc0
    cle
    @5
    @21
    cA
    fveq2
    #
    breq2d
    @30
    @6
    @22
    c1
    cle
    @31
    breq1d
    anbi12d
    imbi2d
    @5
    cK
    wceq
    #
    @9
    @4
    wph
    @32
    @7
    @2
    @8
    @3
    @32
    @6
    @1
    cc0
    cle
    @5
    cK
    cA
    fveq2
    #
    breq2d
    @32
    @6
    @1
    c1
    cle
    @33
    breq1d
    anbi12d
    imbi2d
    @14
    cM
    cL
    cuz
    cfv
    #
    wcel
    #
    wph
    @11
    @12
    wph
    cc0
    cL
    cB
    cfv
    #
    @10
    cle
    wph
    cL
    @0
    wcel
    #
    wph
    @37
    wa
    #
    cc0
    @36
    cle
    wbr
    #
    wph
    @37
    cL
    cL
    cle
    wbr
    #
    cL
    cM
    cle
    wbr
    #
    wph
    cL
    wph
    cL
    fmul01.4
    zred
    leidd
    wph
    @35
    @41
    fmul01.5
    wph
    cL
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    @35
    @41
    wb
    fmul01.4
    wph
    @35
    @43
    fmul01.5
    cL
    cM
    eluzelz
    syl
    #
    cL
    cM
    eluz
    syl2anc
    mpbid
    wph
    @42
    @42
    @43
    @37
    @40
    @41
    wa
    wb
    fmul01.4
    fmul01.4
    @44
    cL
    cL
    cM
    elfz
    syl3anc
    mpbir2and
    #
    wph
    @37
    @45
    ancli
    #
    wph
    vi
    cv
    #
    @0
    wcel
    #
    wa
    #
    cc0
    @47
    cB
    cfv
    #
    cle
    wbr
    #
    wi
    #
    @38
    @39
    wi
    vi
    cL
    @0
    @38
    @39
    vi
    wph
    @37
    vi
    fmul01.2
    @37
    vi
    nfv
    nfan
    #
    vi
    cc0
    @36
    cle
    vi
    cc0
    nfcv
    #
    vi
    cle
    nfcv
    #
    vi
    cL
    cB
    fmul01.1
    vi
    cL
    nfcv
    nffv
    #
    nfbr
    nfim
    @47
    cL
    wceq
    #
    @49
    @38
    @51
    @39
    @57
    @48
    @37
    wph
    @47
    cL
    @0
    eleq1
    anbi2d
    #
    @57
    @50
    @36
    cc0
    cle
    @47
    cL
    cB
    fveq2
    #
    breq2d
    imbi12d
    fmul01.8
    vtoclg1f
    sylc
    wph
    @10
    cL
    cmul
    cB
    cL
    cseq
    #
    cfv
    #
    @36
    cL
    cA
    @60
    fmul01.3
    fveq1i
    wph
    @42
    @61
    @36
    wceq
    fmul01.4
    cmul
    cB
    cL
    seq1
    syl
    syl5eq
    #
    breqtrrd
    wph
    @10
    @36
    c1
    cle
    @62
    wph
    @37
    @38
    @36
    c1
    cle
    wbr
    #
    @45
    @46
    @49
    @50
    c1
    cle
    wbr
    #
    wi
    #
    @38
    @63
    wi
    vi
    cL
    @0
    @38
    @63
    vi
    @53
    vi
    @36
    c1
    cle
    @56
    @55
    vi
    c1
    nfcv
    #
    nfbr
    nfim
    @57
    @49
    @38
    @64
    @63
    @58
    @57
    @50
    @36
    c1
    cle
    @59
    breq1d
    imbi12d
    fmul01.9
    vtoclg1f
    sylc
    eqbrtrd
    jca
    a1i
    @15
    cL
    cM
    cfzo
    co
    wcel
    #
    @20
    wph
    @25
    @67
    @20
    wph
    w3a
    #
    @23
    @24
    @68
    cc0
    @21
    @60
    cfv
    #
    @22
    cle
    @68
    cc0
    @15
    @60
    cfv
    #
    @21
    cB
    cfv
    #
    cmul
    co
    #
    @69
    cle
    @68
    @70
    @71
    @68
    vk
    vl
    cmul
    cr
    cB
    cL
    @15
    @67
    @20
    @15
    @34
    wcel
    #
    wph
    @15
    cL
    cM
    elfzouz
    3ad2ant1
    #
    @68
    @5
    cL
    @15
    cfz
    co
    #
    wcel
    #
    wa
    wph
    @5
    @0
    wcel
    #
    @5
    cB
    cfv
    #
    cr
    wcel
    #
    @67
    @20
    wph
    @76
    simpl3
    @68
    @75
    @0
    @5
    @67
    @20
    @75
    @0
    wss
    #
    wph
    @67
    cM
    @15
    cuz
    cfv
    wcel
    @80
    @15
    cL
    cM
    elfzouz2
    @15
    cL
    cM
    fzss2
    syl
    3ad2ant1
    sselda
    @49
    @50
    cr
    wcel
    #
    wi
    #
    wph
    @77
    wa
    #
    @79
    wi
    vi
    vk
    @83
    @79
    vi
    wph
    @77
    vi
    fmul01.2
    @77
    vi
    nfv
    nfan
    vi
    @78
    cr
    vi
    @5
    cB
    fmul01.1
    vi
    @5
    nfcv
    nffv
    nfel1
    nfim
    @47
    @5
    wceq
    #
    @49
    @83
    @81
    @79
    @84
    @48
    @77
    wph
    @47
    @5
    @0
    eleq1
    anbi2d
    @84
    @50
    @78
    cr
    @47
    @5
    cB
    fveq2
    eleq1d
    imbi12d
    fmul01.7
    chvar
    syl2anc
    @5
    cr
    wcel
    vl
    cv
    #
    cr
    wcel
    wa
    @5
    @85
    cmul
    co
    cr
    wcel
    @68
    @5
    @85
    remulcl
    adantl
    seqcl
    #
    @68
    wph
    @21
    @0
    wcel
    #
    @71
    cr
    wcel
    #
    @67
    @20
    wph
    simp3
    #
    @67
    @20
    @87
    wph
    cL
    cM
    @15
    fzofzp1
    #
    3ad2ant1
    #
    wph
    @87
    @88
    @82
    wph
    @87
    wa
    #
    @88
    wi
    vi
    @21
    @0
    @92
    @88
    vi
    wph
    @87
    vi
    fmul01.2
    @87
    vi
    nfv
    nfan
    #
    vi
    @71
    cr
    vi
    @21
    cB
    fmul01.1
    vi
    @21
    nfcv
    nffv
    #
    nfel1
    nfim
    @47
    @21
    wceq
    #
    @49
    @92
    @81
    @88
    @95
    @48
    @87
    wph
    @47
    @21
    @0
    eleq1
    anbi2d
    #
    @95
    @50
    @71
    cr
    @47
    @21
    cB
    fveq2
    #
    eleq1d
    imbi12d
    fmul01.7
    vtoclg1f
    anabsi7
    syl2anc
    #
    @68
    cc0
    @16
    @70
    cle
    @20
    wph
    @17
    @67
    @20
    wph
    wa
    @19
    @17
    wph
    @20
    @19
    wph
    @19
    pm3.35
    #
    ancoms
    @17
    @18
    simpl
    syl
    3adant1
    @15
    cA
    @60
    fmul01.3
    fveq1i
    #
    syl6breq
    #
    @68
    wph
    @67
    cc0
    @71
    cle
    wbr
    #
    @89
    @67
    @20
    wph
    simp1
    wph
    @67
    wa
    #
    @87
    @92
    @102
    @67
    @87
    wph
    @90
    adantl
    #
    @103
    wph
    @87
    wph
    @67
    simpl
    @104
    jca
    @52
    @92
    @102
    wi
    vi
    @21
    @0
    @92
    @102
    vi
    @93
    vi
    cc0
    @71
    cle
    @54
    @55
    @94
    nfbr
    nfim
    @95
    @49
    @92
    @51
    @102
    @96
    @95
    @50
    @71
    cc0
    cle
    @97
    breq2d
    imbi12d
    fmul01.8
    vtoclg1f
    sylc
    syl2anc
    mulge0d
    @68
    @73
    @69
    @72
    wceq
    @74
    cmul
    cB
    cL
    @15
    seqp1
    syl
    #
    breqtrrd
    @21
    cA
    @60
    fmul01.3
    fveq1i
    #
    syl6breqr
    @68
    @22
    @69
    c1
    cle
    @106
    @68
    @69
    @72
    c1
    cle
    @105
    @68
    @72
    @70
    c1
    @68
    @70
    @71
    @86
    @98
    remulcld
    @86
    @68
    1red
    #
    @68
    @72
    @70
    c1
    cmul
    co
    @70
    cle
    @68
    @71
    c1
    @70
    @98
    @107
    @86
    @101
    @68
    @87
    @92
    @71
    c1
    cle
    wbr
    #
    @91
    @68
    wph
    @87
    @89
    @91
    jca
    @65
    @92
    @108
    wi
    vi
    @21
    @0
    @92
    @108
    vi
    @93
    vi
    @71
    c1
    cle
    @94
    @55
    @66
    nfbr
    nfim
    @95
    @49
    @92
    @64
    @108
    @96
    @95
    @50
    @71
    c1
    cle
    @97
    breq1d
    imbi12d
    fmul01.9
    vtoclg1f
    sylc
    lemul2ad
    @68
    @70
    @68
    @70
    @86
    recnd
    mulid1d
    breqtrd
    @68
    @70
    @16
    c1
    cle
    @100
    @68
    wph
    @20
    @18
    @89
    @67
    @20
    wph
    simp2
    wph
    @20
    wa
    @17
    @18
    @99
    simprd
    syl2anc
    syl5eqbrr
    letrd
    eqbrtrd
    syl5eqbr
    jca
    3exp
    fzind2
    mpcom
end
