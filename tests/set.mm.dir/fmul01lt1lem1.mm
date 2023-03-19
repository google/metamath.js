include "wceq.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cmul.mm"
include "cseq.mm"
include "simpr.mm"
include "fveq2d.mm"
include "a1i.mm"
include "fveq1d.mm"
include "cz.mm"
include "wcel.mm"
include "seq1.mm"
include "syl.mm"
include "adantr.mm"
include "3eqtrd.mm"
include "eqbrtrd.mm"
include "wn.mm"
include "wne.mm"
include "neqned.mm"
include "cr.mm"
include "cle.mm"
include "w3a.mm"
include "wb.mm"
include "zred.mm"
include "cuz.mm"
include "eluzelz.mm"
include "eluzle.mm"
include "3jca.mm"
include "leltne.mm"
include "mpbird.mm"
include "fveq1i.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cv.mm"
include "remulcl.mm"
include "adantl.mm"
include "cc.mm"
include "recn.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "mulassd.mm"
include "wo.mm"
include "olcd.mm"
include "jca.mm"
include "lttri2.mm"
include "neneqd.mm"
include "uzp1.mm"
include "ord.mm"
include "mpd.mm"
include "uzid.mm"
include "cfz.mm"
include "wi.mm"
include "nfv.mm"
include "nfan.mm"
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
include "adantlr.mm"
include "seqsplit.mm"
include "eluzfz1.mm"
include "ancli.mm"
include "vtoclg1f.mm"
include "sylc.mm"
include "eqeltrd.mm"
include "elfzelz.mm"
include "peano2re.mm"
include "lep1d.mm"
include "elfzle1.mm"
include "letrd.mm"
include "elfzle2.mm"
include "elfz2.mm"
include "sylanbrc.mm"
include "syldan.mm"
include "seqcl.mm"
include "remulcld.mm"
include "rpred.mm"
include "1red.mm"
include "cc0.mm"
include "nfbr.mm"
include "breq2d.mm"
include "breqtrrd.mm"
include "eqid.mm"
include "peano2zd.mm"
include "gtned.mm"
include "orel1.mm"
include "zltp1le.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "leidd.mm"
include "simpll.mm"
include "ad2antrr.mm"
include "fmul01.mm"
include "simprd.mm"
include "lemul2ad.mm"
include "recnd.mm"
include "mulid1d.mm"
include "breqtrd.mm"
include "lelttrd.mm"
include "syl5eqbr.mm"
include "pm2.61dan.mm"

theorem fmul01lt1lem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vi: setvar i
  let cE: class E
  let cL: class L
  let cM: class M
  let vj: setvar j
  let vk: setvar k
  let vl: setvar l
  assume fmul01lt1lem1.1: |- F/_ i B
  assume fmul01lt1lem1.2: |- F/ i ph
  assume fmul01lt1lem1.3: |- A = seq L ( x. , B )
  assume fmul01lt1lem1.4: |- ( ph -> L e. ZZ )
  assume fmul01lt1lem1.5: |- ( ph -> M e. ( ZZ>= ` L ) )
  assume fmul01lt1lem1.6: |- ( ( ph /\ i e. ( L ... M ) ) -> ( B ` i ) e. RR )
  assume fmul01lt1lem1.7: |- ( ( ph /\ i e. ( L ... M ) ) -> 0 <_ ( B ` i ) )
  assume fmul01lt1lem1.8: |- ( ( ph /\ i e. ( L ... M ) ) -> ( B ` i ) <_ 1 )
  assume fmul01lt1lem1.9: |- ( ph -> E e. RR+ )
  assume fmul01lt1lem1.10: |- ( ph -> ( B ` L ) < E )

  disjoint L i
  disjoint M i
  disjoint i j
  disjoint L j
  disjoint M j
  disjoint j k
  disjoint j l
  disjoint B j
  disjoint k l
  disjoint B k
  disjoint B l
  disjoint j ph
  disjoint k ph
  disjoint l ph
  disjoint L k
  disjoint L l
  disjoint M k
  disjoint M l
  assert |- ( ph -> ( A ` M ) < E )

  proof
    wph
    cM
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
    #
    wph
    @0
    wa
    #
    @1
    cL
    cB
    cfv
    #
    cE
    clt
    @3
    @1
    cL
    cA
    cfv
    cL
    cmul
    cB
    cL
    cseq
    #
    cfv
    #
    @4
    @3
    cM
    cL
    cA
    wph
    @0
    simpr
    fveq2d
    @3
    cL
    cA
    @5
    cA
    @5
    wceq
    @3
    fmul01lt1lem1.3
    a1i
    fveq1d
    wph
    @6
    @4
    wceq
    #
    @0
    wph
    cL
    cz
    wcel
    #
    @7
    fmul01lt1lem1.4
    cmul
    cB
    cL
    seq1
    syl
    #
    adantr
    3eqtrd
    wph
    @4
    cE
    clt
    wbr
    @0
    fmul01lt1lem1.10
    adantr
    eqbrtrd
    wph
    @0
    wn
    #
    cL
    cM
    clt
    wbr
    #
    @2
    wph
    @10
    wa
    #
    @11
    cM
    cL
    wne
    #
    @12
    cM
    cL
    wph
    @10
    simpr
    neqned
    @12
    cL
    cr
    wcel
    #
    cM
    cr
    wcel
    #
    cL
    cM
    cle
    wbr
    #
    w3a
    #
    @11
    @13
    wb
    wph
    @17
    @10
    wph
    @14
    @15
    @16
    wph
    cL
    fmul01lt1lem1.4
    zred
    #
    wph
    cM
    wph
    cM
    cL
    cuz
    cfv
    #
    wcel
    #
    cM
    cz
    wcel
    #
    fmul01lt1lem1.5
    cL
    cM
    eluzelz
    syl
    #
    zred
    #
    wph
    @20
    @16
    fmul01lt1lem1.5
    cL
    cM
    eluzle
    syl
    3jca
    adantr
    cL
    cM
    leltne
    syl
    mpbird
    wph
    @11
    wa
    #
    @1
    cM
    @5
    cfv
    #
    cE
    clt
    cM
    cA
    @5
    fmul01lt1lem1.3
    fveq1i
    @24
    @25
    @6
    cM
    cmul
    cB
    cL
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
    #
    cE
    clt
    @24
    vj
    vk
    vl
    cmul
    cr
    cB
    cL
    cL
    cM
    vj
    cv
    #
    cr
    wcel
    #
    vk
    cv
    #
    cr
    wcel
    #
    wa
    @30
    @32
    cmul
    co
    #
    cr
    wcel
    @24
    @30
    @32
    remulcl
    adantl
    #
    @31
    @33
    vl
    cv
    #
    cr
    wcel
    #
    w3a
    #
    @34
    @36
    cmul
    co
    @30
    @32
    @36
    cmul
    co
    cmul
    co
    wceq
    @24
    @38
    @30
    @32
    @36
    @31
    @33
    @30
    cc
    wcel
    @37
    @30
    recn
    3ad2ant1
    @33
    @31
    @32
    cc
    wcel
    @37
    @32
    recn
    3ad2ant2
    @37
    @31
    @36
    cc
    wcel
    @33
    @36
    recn
    3ad2ant3
    mulassd
    adantl
    @24
    @10
    cM
    @26
    cuz
    cfv
    wcel
    #
    @24
    cM
    cL
    @24
    @13
    cM
    cL
    clt
    wbr
    #
    @11
    wo
    #
    @24
    @11
    @40
    wph
    @11
    simpr
    #
    olcd
    @24
    @15
    @14
    wa
    #
    @13
    @41
    wb
    wph
    @43
    @11
    wph
    @15
    @14
    @23
    @18
    jca
    adantr
    cM
    cL
    lttri2
    syl
    mpbird
    neneqd
    @24
    @0
    @39
    wph
    @0
    @39
    wo
    #
    @11
    wph
    @20
    @44
    fmul01lt1lem1.5
    cL
    cM
    uzp1
    #
    syl
    adantr
    ord
    mpd
    #
    @24
    @8
    cL
    @19
    wcel
    wph
    @8
    @11
    fmul01lt1lem1.4
    adantr
    #
    cL
    uzid
    syl
    wph
    @30
    cL
    cM
    cfz
    co
    #
    wcel
    #
    @30
    cB
    cfv
    #
    cr
    wcel
    #
    @11
    wph
    vi
    cv
    #
    @48
    wcel
    #
    wa
    #
    @52
    cB
    cfv
    #
    cr
    wcel
    #
    wi
    #
    wph
    @49
    wa
    #
    @51
    wi
    vi
    vj
    @58
    @51
    vi
    wph
    @49
    vi
    fmul01lt1lem1.2
    @49
    vi
    nfv
    nfan
    vi
    @50
    cr
    vi
    @30
    cB
    fmul01lt1lem1.1
    vi
    @30
    nfcv
    nffv
    nfel1
    nfim
    @52
    @30
    wceq
    #
    @54
    @58
    @56
    @51
    @59
    @53
    @49
    wph
    @52
    @30
    @48
    eleq1
    anbi2d
    @59
    @55
    @50
    cr
    @52
    @30
    cB
    fveq2
    eleq1d
    imbi12d
    fmul01lt1lem1.6
    chvar
    #
    adantlr
    seqsplit
    @24
    @29
    @6
    cE
    @24
    @6
    @28
    wph
    @6
    cr
    wcel
    @11
    wph
    @6
    @4
    cr
    @9
    wph
    cL
    @48
    wcel
    #
    wph
    @61
    wa
    #
    @4
    cr
    wcel
    #
    wph
    @20
    @61
    fmul01lt1lem1.5
    cL
    cM
    eluzfz1
    syl
    #
    wph
    @61
    @64
    ancli
    #
    @57
    @62
    @63
    wi
    vi
    cL
    @48
    @62
    @63
    vi
    wph
    @61
    vi
    fmul01lt1lem1.2
    @61
    vi
    nfv
    nfan
    #
    vi
    @4
    cr
    vi
    cL
    cB
    fmul01lt1lem1.1
    vi
    cL
    nfcv
    nffv
    #
    nfel1
    nfim
    @52
    cL
    wceq
    #
    @54
    @62
    @56
    @63
    @68
    @53
    @61
    wph
    @52
    cL
    @48
    eleq1
    anbi2d
    #
    @68
    @55
    @4
    cr
    @52
    cL
    cB
    fveq2
    #
    eleq1d
    imbi12d
    fmul01lt1lem1.6
    vtoclg1f
    sylc
    eqeltrd
    #
    adantr
    #
    @24
    vj
    vk
    cmul
    cr
    cB
    @26
    cM
    @46
    wph
    @30
    @26
    cM
    cfz
    co
    #
    wcel
    #
    @51
    @11
    wph
    @74
    @49
    @51
    wph
    @74
    wa
    #
    @8
    @21
    @30
    cz
    wcel
    #
    w3a
    cL
    @30
    cle
    wbr
    #
    @30
    cM
    cle
    wbr
    #
    wa
    @49
    @75
    @8
    @21
    @76
    wph
    @8
    @74
    fmul01lt1lem1.4
    adantr
    wph
    @21
    @74
    @22
    adantr
    @74
    @76
    wph
    @30
    @26
    cM
    elfzelz
    #
    adantl
    3jca
    @75
    @77
    @78
    @75
    cL
    @26
    @30
    wph
    @14
    @74
    @18
    adantr
    wph
    @26
    cr
    wcel
    #
    @74
    wph
    @14
    @80
    @18
    cL
    peano2re
    #
    syl
    #
    adantr
    @74
    @31
    wph
    @74
    @30
    @79
    zred
    adantl
    wph
    cL
    @26
    cle
    wbr
    #
    @74
    wph
    cL
    @18
    lep1d
    #
    adantr
    @74
    @26
    @30
    cle
    wbr
    wph
    @30
    @26
    cM
    elfzle1
    adantl
    letrd
    @74
    @78
    wph
    @30
    @26
    cM
    elfzle2
    adantl
    jca
    @30
    cL
    cM
    elfz2
    sylanbrc
    @60
    syldan
    adantlr
    @35
    seqcl
    #
    remulcld
    @72
    wph
    cE
    cr
    wcel
    @11
    wph
    cE
    fmul01lt1lem1.9
    rpred
    adantr
    @24
    @29
    @6
    c1
    cmul
    co
    #
    @6
    cle
    @24
    @28
    c1
    @6
    @85
    @24
    1red
    @72
    wph
    cc0
    @6
    cle
    wbr
    @11
    wph
    cc0
    @4
    @6
    cle
    wph
    @61
    @62
    cc0
    @4
    cle
    wbr
    #
    @64
    @65
    @54
    cc0
    @55
    cle
    wbr
    #
    wi
    @62
    @87
    wi
    vi
    cL
    @48
    @62
    @87
    vi
    @66
    vi
    cc0
    @4
    cle
    vi
    cc0
    nfcv
    vi
    cle
    nfcv
    @67
    nfbr
    nfim
    @68
    @54
    @62
    @88
    @87
    @69
    @68
    @55
    @4
    cc0
    cle
    @70
    breq2d
    imbi12d
    fmul01lt1lem1.7
    vtoclg1f
    sylc
    @9
    breqtrrd
    adantr
    @24
    cc0
    @28
    cle
    wbr
    @28
    c1
    cle
    wbr
    @24
    @27
    cB
    vi
    cM
    @26
    cM
    fmul01lt1lem1.1
    wph
    @11
    vi
    fmul01lt1lem1.2
    @11
    vi
    nfv
    nfan
    @27
    eqid
    wph
    @26
    cz
    wcel
    #
    @11
    wph
    cL
    fmul01lt1lem1.4
    peano2zd
    adantr
    #
    @24
    @10
    @44
    @39
    @24
    cM
    cL
    @24
    cL
    cM
    wph
    @14
    @11
    @18
    adantr
    @42
    gtned
    neneqd
    @24
    @20
    @44
    wph
    @20
    @11
    fmul01lt1lem1.5
    adantr
    @45
    syl
    @0
    @39
    orel1
    sylc
    @24
    @89
    @21
    @21
    w3a
    @26
    cM
    cle
    wbr
    #
    cM
    cM
    cle
    wbr
    #
    wa
    cM
    @73
    wcel
    @24
    @89
    @21
    @21
    @90
    wph
    @21
    @11
    @22
    adantr
    #
    @93
    3jca
    @24
    @91
    @92
    @24
    @11
    @91
    @42
    @24
    @8
    @21
    @11
    @91
    wb
    @47
    @93
    cL
    cM
    zltp1le
    syl2anc
    mpbid
    @24
    cM
    wph
    @15
    @11
    @23
    adantr
    leidd
    jca
    cM
    @26
    cM
    elfz2
    sylanbrc
    wph
    @52
    @73
    wcel
    #
    @56
    @11
    wph
    @94
    @53
    @56
    wph
    @94
    wa
    #
    @8
    @21
    @52
    cz
    wcel
    #
    w3a
    #
    cL
    @52
    cle
    wbr
    #
    @52
    cM
    cle
    wbr
    #
    wa
    #
    @53
    @95
    @8
    @21
    @96
    wph
    @8
    @94
    fmul01lt1lem1.4
    adantr
    wph
    @21
    @94
    @22
    adantr
    @94
    @96
    wph
    @52
    @26
    cM
    elfzelz
    #
    adantl
    3jca
    @95
    @98
    @99
    @95
    cL
    @26
    @52
    wph
    @14
    @94
    @18
    adantr
    #
    @95
    @14
    @80
    @102
    @81
    syl
    @94
    @52
    cr
    wcel
    #
    wph
    @94
    @52
    @101
    zred
    #
    adantl
    wph
    @83
    @94
    @84
    adantr
    @94
    @26
    @52
    cle
    wbr
    #
    wph
    @52
    @26
    cM
    elfzle1
    #
    adantl
    letrd
    @94
    @99
    wph
    @52
    @26
    cM
    elfzle2
    #
    adantl
    jca
    @52
    cL
    cM
    elfz2
    #
    sylanbrc
    fmul01lt1lem1.6
    syldan
    adantlr
    @24
    @94
    wa
    #
    wph
    @53
    @88
    wph
    @11
    @94
    simpll
    #
    @109
    @97
    @100
    @53
    @109
    @8
    @21
    @96
    wph
    @8
    @11
    @94
    fmul01lt1lem1.4
    ad2antrr
    wph
    @21
    @11
    @94
    @22
    ad2antrr
    @94
    @96
    @24
    @101
    adantl
    3jca
    @109
    @98
    @99
    @109
    cL
    @26
    @52
    wph
    @14
    @11
    @94
    @18
    ad2antrr
    wph
    @80
    @11
    @94
    @82
    ad2antrr
    @94
    @103
    @24
    @104
    adantl
    wph
    @83
    @11
    @94
    @84
    ad2antrr
    @94
    @105
    @24
    @106
    adantl
    letrd
    @94
    @99
    @24
    @107
    adantl
    jca
    @108
    sylanbrc
    #
    fmul01lt1lem1.7
    syl2anc
    @109
    wph
    @53
    @55
    c1
    cle
    wbr
    @110
    @111
    fmul01lt1lem1.8
    syl2anc
    fmul01
    simprd
    lemul2ad
    wph
    @86
    @6
    wceq
    @11
    wph
    @6
    wph
    @6
    @71
    recnd
    mulid1d
    adantr
    breqtrd
    wph
    @6
    cE
    clt
    wbr
    @11
    wph
    @6
    @4
    cE
    clt
    @9
    fmul01lt1lem1.10
    eqbrtrd
    adantr
    lelttrd
    eqbrtrd
    syl5eqbr
    syldan
    pm2.61dan
end
