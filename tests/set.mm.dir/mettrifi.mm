include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "cv.mm"
include "caddc.mm"
include "csu.mm"
include "cle.mm"
include "wbr.mm"
include "cuz.mm"
include "eluzfz2.mm"
include "syl.mm"
include "wi.mm"
include "wceq.mm"
include "eleq1.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "oveq1.mm"
include "sumeq1d.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "cz.mm"
include "cc0.mm"
include "0le0.mm"
include "a1i.mm"
include "cme.mm"
include "wral.mm"
include "eluzfz1.mm"
include "ralrimiva.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "met0.mm"
include "syl2anc.mm"
include "c0.mm"
include "clt.mm"
include "eluzel2.mm"
include "zred.mm"
include "ltm1d.mm"
include "wb.mm"
include "peano2zm.mm"
include "fzn.mm"
include "mpbid.mm"
include "sum0.mm"
include "syl6eq.mm"
include "3brtr4d.mm"
include "a1d.mm"
include "wa.mm"
include "peano2fzr.mm"
include "ex.mm"
include "adantl.mm"
include "imim1d.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "cbvralv.mm"
include "sylib.mm"
include "3impia.mm"
include "rsp.mm"
include "mettri.mm"
include "syl13anc.mm"
include "cr.mm"
include "metcl.mm"
include "syl3anc.mm"
include "readdcld.mm"
include "fzfid.mm"
include "adantr.mm"
include "wss.mm"
include "elfzuz3.mm"
include "fzss2.mm"
include "sselda.mm"
include "3ad2antl1.mm"
include "syldan.mm"
include "elfzuz.mm"
include "peano2uz.mm"
include "eluzp1p1.mm"
include "uztrn.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "rspccva.mm"
include "sylan.mm"
include "fsumrecl.mm"
include "letr.mm"
include "mpand.mm"
include "fzssp1.mm"
include "cc.mm"
include "eluzelz.mm"
include "3ad2ant2.mm"
include "zcnd.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "syl5sseq.mm"
include "leadd1d.mm"
include "simp2.mm"
include "recnd.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "fsumm1.mm"
include "breq2d.mm"
include "bitr4d.mm"
include "pncan.mm"
include "3imtr4d.mm"
include "3expia.mm"
include "a2d.mm"
include "syld.mm"
include "expcom.mm"
include "uzind4.mm"
include "mpcom.mm"
include "mpd.mm"

theorem mettrifi
  let wph: wff ph
  let cD: class D
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let cX: class X
  let vn: setvar n
  let vx: setvar x
  assume mettrifi.2: |- ( ph -> D e. ( Met ` X ) )
  assume mettrifi.3: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume mettrifi.4: |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) e. X )

  disjoint D k
  disjoint F k
  disjoint M k
  disjoint N k
  disjoint k ph
  disjoint X k
  disjoint k n
  disjoint k x
  disjoint n x
  disjoint D n
  disjoint D x
  disjoint F n
  disjoint F x
  disjoint M n
  disjoint M x
  disjoint N n
  disjoint N x
  disjoint n ph
  disjoint ph x
  disjoint X n
  assert |- ( ph -> ( ( F ` M ) D ( F ` N ) ) <_ sum_ k e. ( M ... ( N - 1 ) ) ( ( F ` k ) D ( F ` ( k + 1 ) ) ) )

  proof
    wph
    cN
    cM
    cN
    cfz
    co
    #
    wcel
    #
    cM
    cF
    cfv
    #
    cN
    cF
    cfv
    #
    cD
    co
    #
    cM
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    vk
    cv
    #
    cF
    cfv
    #
    @7
    c1
    caddc
    co
    #
    cF
    cfv
    #
    cD
    co
    #
    vk
    csu
    #
    cle
    wbr
    #
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    @1
    mettrifi.3
    cM
    cN
    eluzfz2
    syl
    @15
    wph
    @1
    @13
    wi
    #
    mettrifi.3
    wph
    vx
    cv
    #
    @0
    wcel
    #
    @2
    @17
    cF
    cfv
    #
    cD
    co
    #
    cM
    @17
    c1
    cmin
    co
    #
    cfz
    co
    #
    @11
    vk
    csu
    #
    cle
    wbr
    #
    wi
    #
    wi
    wph
    cM
    @0
    wcel
    #
    @2
    @2
    cD
    co
    #
    cM
    cM
    c1
    cmin
    co
    #
    cfz
    co
    #
    @11
    vk
    csu
    #
    cle
    wbr
    #
    wi
    #
    wi
    #
    wph
    vn
    cv
    #
    @0
    wcel
    #
    @2
    @34
    cF
    cfv
    #
    cD
    co
    #
    cM
    @34
    c1
    cmin
    co
    #
    cfz
    co
    #
    @11
    vk
    csu
    #
    cle
    wbr
    #
    wi
    #
    wi
    wph
    @34
    c1
    caddc
    co
    #
    @0
    wcel
    #
    @2
    @43
    cF
    cfv
    #
    cD
    co
    #
    cM
    @43
    c1
    cmin
    co
    #
    cfz
    co
    #
    @11
    vk
    csu
    #
    cle
    wbr
    #
    wi
    #
    wi
    wph
    @16
    wi
    vx
    vn
    cM
    cN
    @17
    cM
    wceq
    #
    @25
    @32
    wph
    @52
    @18
    @26
    @24
    @31
    @17
    cM
    @0
    eleq1
    @52
    @20
    @27
    @23
    @30
    cle
    @52
    @19
    @2
    @2
    cD
    @17
    cM
    cF
    fveq2
    oveq2d
    @52
    @22
    @29
    @11
    vk
    @52
    @21
    @28
    cM
    cfz
    @17
    cM
    c1
    cmin
    oveq1
    oveq2d
    sumeq1d
    breq12d
    imbi12d
    imbi2d
    @17
    @34
    wceq
    #
    @25
    @42
    wph
    @53
    @18
    @35
    @24
    @41
    @17
    @34
    @0
    eleq1
    @53
    @20
    @37
    @23
    @40
    cle
    @53
    @19
    @36
    @2
    cD
    @17
    @34
    cF
    fveq2
    oveq2d
    @53
    @22
    @39
    @11
    vk
    @53
    @21
    @38
    cM
    cfz
    @17
    @34
    c1
    cmin
    oveq1
    oveq2d
    sumeq1d
    breq12d
    imbi12d
    imbi2d
    @17
    @43
    wceq
    #
    @25
    @51
    wph
    @54
    @18
    @44
    @24
    @50
    @17
    @43
    @0
    eleq1
    @54
    @20
    @46
    @23
    @49
    cle
    @54
    @19
    @45
    @2
    cD
    @17
    @43
    cF
    fveq2
    oveq2d
    @54
    @22
    @48
    @11
    vk
    @54
    @21
    @47
    cM
    cfz
    @17
    @43
    c1
    cmin
    oveq1
    oveq2d
    sumeq1d
    breq12d
    imbi12d
    imbi2d
    @17
    cN
    wceq
    #
    @25
    @16
    wph
    @55
    @18
    @1
    @24
    @13
    @17
    cN
    @0
    eleq1
    @55
    @20
    @4
    @23
    @12
    cle
    @55
    @19
    @3
    @2
    cD
    @17
    cN
    cF
    fveq2
    oveq2d
    @55
    @22
    @6
    @11
    vk
    @55
    @21
    @5
    cM
    cfz
    @17
    cN
    c1
    cmin
    oveq1
    oveq2d
    sumeq1d
    breq12d
    imbi12d
    imbi2d
    @33
    cM
    cz
    wcel
    #
    wph
    @31
    @26
    wph
    cc0
    cc0
    @27
    @30
    cle
    cc0
    cc0
    cle
    wbr
    wph
    0le0
    a1i
    wph
    cD
    cX
    cme
    cfv
    wcel
    #
    @2
    cX
    wcel
    #
    @27
    cc0
    wceq
    mettrifi.2
    wph
    @26
    @8
    cX
    wcel
    #
    vk
    @0
    wral
    #
    @58
    wph
    @15
    @26
    mettrifi.3
    cM
    cN
    eluzfz1
    syl
    wph
    @59
    vk
    @0
    mettrifi.4
    ralrimiva
    #
    @59
    @58
    vk
    cM
    @0
    @7
    cM
    wceq
    @8
    @2
    cX
    @7
    cM
    cF
    fveq2
    eleq1d
    rspcv
    sylc
    #
    @2
    cD
    cX
    met0
    syl2anc
    wph
    @30
    c0
    @11
    vk
    csu
    cc0
    wph
    @29
    c0
    @11
    vk
    wph
    @28
    cM
    clt
    wbr
    #
    @29
    c0
    wceq
    #
    wph
    cM
    wph
    cM
    wph
    @15
    @56
    mettrifi.3
    cM
    cN
    eluzel2
    syl
    #
    zred
    ltm1d
    wph
    @56
    @28
    cz
    wcel
    #
    @63
    @64
    wb
    @65
    wph
    @56
    @66
    @65
    cM
    peano2zm
    syl
    cM
    @28
    fzn
    syl2anc
    mpbid
    sumeq1d
    @11
    vk
    sum0
    syl6eq
    3brtr4d
    a1d
    a1i
    @34
    @14
    wcel
    #
    wph
    @42
    @51
    wph
    @67
    @42
    @51
    wi
    wph
    @67
    wa
    #
    @42
    @44
    @41
    wi
    @51
    @68
    @44
    @35
    @41
    @67
    @44
    @35
    wi
    wph
    @67
    @44
    @35
    @34
    cM
    cN
    peano2fzr
    ex
    adantl
    #
    imim1d
    @68
    @44
    @41
    @50
    wph
    @67
    @44
    @41
    @50
    wi
    wph
    @67
    @44
    w3a
    #
    @37
    @36
    @45
    cD
    co
    #
    caddc
    co
    #
    cM
    @34
    cfz
    co
    #
    @11
    vk
    csu
    #
    cle
    wbr
    #
    @46
    @74
    cle
    wbr
    #
    @41
    @50
    @70
    @46
    @72
    cle
    wbr
    #
    @75
    @76
    @70
    @57
    @58
    @45
    cX
    wcel
    #
    @36
    cX
    wcel
    #
    @77
    wph
    @67
    @57
    @44
    mettrifi.2
    3ad2ant1
    #
    wph
    @67
    @58
    @44
    @62
    3ad2ant1
    #
    @70
    @44
    @60
    @78
    wph
    @67
    @44
    simp3
    #
    wph
    @67
    @60
    @44
    @61
    3ad2ant1
    #
    @59
    @78
    vk
    @43
    @0
    @7
    @43
    wceq
    @8
    @45
    cX
    @7
    @43
    cF
    fveq2
    eleq1d
    rspcv
    sylc
    #
    @70
    @79
    vn
    @0
    wral
    #
    @35
    @79
    @70
    @60
    @85
    @83
    @59
    @79
    vk
    vn
    @0
    @7
    @34
    wceq
    #
    @8
    @36
    cX
    @7
    @34
    cF
    fveq2
    #
    eleq1d
    cbvralv
    sylib
    #
    wph
    @67
    @44
    @35
    @69
    3impia
    #
    @79
    vn
    @0
    rsp
    sylc
    #
    @2
    @45
    @36
    cD
    cX
    mettri
    syl13anc
    @70
    @46
    cr
    wcel
    #
    @72
    cr
    wcel
    @74
    cr
    wcel
    @77
    @75
    wa
    @76
    wi
    @70
    @57
    @58
    @78
    @91
    @80
    @81
    @84
    @2
    @45
    cD
    cX
    metcl
    syl3anc
    @70
    @37
    @71
    @70
    @57
    @58
    @79
    @37
    cr
    wcel
    @80
    @81
    @90
    @2
    @36
    cD
    cX
    metcl
    syl3anc
    #
    @70
    @57
    @79
    @78
    @71
    cr
    wcel
    @80
    @90
    @84
    @36
    @45
    cD
    cX
    metcl
    syl3anc
    #
    readdcld
    @70
    @73
    @11
    vk
    @70
    cM
    @34
    fzfid
    @70
    @7
    @73
    wcel
    #
    wa
    #
    @57
    @59
    @10
    cX
    wcel
    #
    @11
    cr
    wcel
    #
    @70
    @57
    @94
    @80
    adantr
    @70
    @94
    @7
    @0
    wcel
    #
    @59
    @70
    @73
    @0
    @7
    @70
    cN
    @34
    cuz
    cfv
    wcel
    #
    @73
    @0
    wss
    @70
    @35
    @99
    @89
    @34
    cM
    cN
    elfzuz3
    syl
    @34
    cM
    cN
    fzss2
    syl
    sselda
    wph
    @67
    @98
    @59
    @44
    mettrifi.4
    3ad2antl1
    syldan
    @70
    @94
    @9
    @0
    wcel
    #
    @96
    @95
    @9
    @14
    wcel
    #
    cN
    @9
    cuz
    cfv
    #
    wcel
    #
    @100
    @95
    @7
    @14
    wcel
    #
    @101
    @94
    @104
    @70
    @7
    cM
    @34
    elfzuz
    adantl
    cM
    @7
    peano2uz
    syl
    @95
    cN
    @43
    cuz
    cfv
    wcel
    #
    @43
    @102
    wcel
    #
    @103
    @70
    @105
    @94
    @70
    @44
    @105
    @82
    @43
    cM
    cN
    elfzuz3
    syl
    adantr
    @95
    @34
    @7
    cuz
    cfv
    wcel
    #
    @106
    @94
    @107
    @70
    @7
    cM
    @34
    elfzuz3
    adantl
    @7
    @34
    eluzp1p1
    syl
    @43
    cN
    @9
    uztrn
    syl2anc
    @9
    cM
    cN
    elfzuzb
    sylanbrc
    @70
    @85
    @100
    @96
    @88
    @79
    @96
    vn
    @9
    @0
    @34
    @9
    wceq
    @36
    @10
    cX
    @34
    @9
    cF
    fveq2
    eleq1d
    rspccva
    sylan
    syldan
    @8
    @10
    cD
    cX
    metcl
    syl3anc
    #
    fsumrecl
    @46
    @72
    @74
    letr
    syl3anc
    mpand
    @70
    @41
    @72
    @40
    @71
    caddc
    co
    #
    cle
    wbr
    @75
    @70
    @37
    @40
    @71
    @92
    @70
    @39
    @11
    vk
    @70
    cM
    @38
    fzfid
    @70
    @7
    @39
    wcel
    @94
    @97
    @70
    @39
    @73
    @7
    @70
    cM
    @38
    c1
    caddc
    co
    #
    cfz
    co
    @39
    @73
    cM
    @38
    fzssp1
    @70
    @110
    @34
    cM
    cfz
    @70
    @34
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @110
    @34
    wceq
    @70
    @34
    @67
    wph
    @34
    cz
    wcel
    @44
    cM
    @34
    eluzelz
    3ad2ant2
    zcnd
    #
    ax-1cn
    @34
    c1
    npcan
    sylancl
    oveq2d
    syl5sseq
    sselda
    @108
    syldan
    fsumrecl
    @93
    leadd1d
    @70
    @74
    @109
    @72
    cle
    @70
    @11
    @71
    vk
    cM
    @34
    wph
    @67
    @44
    simp2
    @95
    @11
    @108
    recnd
    @86
    @8
    @36
    @10
    @45
    cD
    @87
    @86
    @9
    @43
    cF
    @7
    @34
    c1
    caddc
    oveq1
    fveq2d
    oveq12d
    fsumm1
    breq2d
    bitr4d
    @70
    @49
    @74
    @46
    cle
    @70
    @48
    @73
    @11
    vk
    @70
    @47
    @34
    cM
    cfz
    @70
    @111
    @112
    @47
    @34
    wceq
    @113
    ax-1cn
    @34
    c1
    pncan
    sylancl
    oveq2d
    sumeq1d
    breq2d
    3imtr4d
    3expia
    a2d
    syld
    expcom
    a2d
    uzind4
    mpcom
    mpd
end
