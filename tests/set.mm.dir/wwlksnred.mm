include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cwwlksn.mm"
include "cwwlks.mm"
include "cfv.mm"
include "chash.mm"
include "wceq.mm"
include "wa.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "wb.mm"
include "peano2nn0.mm"
include "iswwlksn.mm"
include "syl.mm"
include "c0.mm"
include "wne.mm"
include "cvtx.mm"
include "cword.mm"
include "cv.mm"
include "cpr.mm"
include "cedg.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "wi.mm"
include "eqid.mm"
include "iswwlks.mm"
include "cn.mm"
include "cle.mm"
include "wbr.mm"
include "simp1.mm"
include "nn0p1nn.mm"
include "3ad2ant3.mm"
include "nn0red.mm"
include "lep1d.mm"
include "breq2.mm"
include "3ad2ant2.mm"
include "mpbird.mm"
include "swrdn0.mm"
include "syl3anc.mm"
include "3exp.mm"
include "imp.mm"
include "impcom.mm"
include "swrdcl.mm"
include "adantr.mm"
include "adantl.mm"
include "oveq1.mm"
include "nn0cnd.mm"
include "1cnd.mm"
include "pncand.mm"
include "sylan9eq.mm"
include "oveq2d.mm"
include "raleqdv.mm"
include "wss.mm"
include "cuz.mm"
include "cz.mm"
include "nn0z.mm"
include "nn0re.mm"
include "3jca.mm"
include "ad2antll.mm"
include "eluz2.mm"
include "sylibr.mm"
include "fzoss2.mm"
include "ssralv.mm"
include "cfz.mm"
include "simpl.mm"
include "nn0fz0.mm"
include "sylib.mm"
include "fzelp1.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "fzossfzop1.mm"
include "sseld.mm"
include "swrd0fv.mm"
include "eqcomd.mm"
include "fzofzp1.mm"
include "fzval3.mm"
include "preq12d.mm"
include "eleq1d.mm"
include "biimpd.mm"
include "ralimdva.mm"
include "syld.mm"
include "sylbid.mm"
include "nn0cn.mm"
include "swrd0len0.mm"
include "oveq1d.mm"
include "exp31.mm"
include "com23.mm"
include "3adant1.mm"
include "expdimp.mm"
include "syl3anbrc.mm"
include "elfz2nn0.mm"
include "anim2i.mm"
include "exp32.mm"
include "swrd0len.mm"
include "mpbir2and.mm"
include "expcom.mm"
include "sylanb.mm"
include "com12.mm"

theorem wwlksnred
  let cG: class G
  let cN: class N
  let cW: class W
  let vi: setvar i


  assert |- ( N e. NN0 -> ( W e. ( ( N + 1 ) WWalksN G ) -> ( W substr <. 0 , ( N + 1 ) >. ) e. ( N WWalksN G ) ) )

  proof
    cN
    cn0
    wcel
    #
    cW
    cN
    c1
    caddc
    co
    #
    cG
    cwwlksn
    co
    wcel
    #
    cW
    cG
    cwwlks
    cfv
    #
    wcel
    #
    cW
    chash
    cfv
    #
    @1
    c1
    caddc
    co
    #
    wceq
    #
    wa
    #
    cW
    cc0
    @1
    cop
    csubstr
    co
    #
    cN
    cG
    cwwlksn
    co
    wcel
    #
    @0
    @1
    cn0
    wcel
    #
    @2
    @8
    wb
    cN
    peano2nn0
    #
    cG
    @1
    cW
    iswwlksn
    syl
    @8
    @0
    @10
    @4
    cW
    c0
    wne
    #
    cW
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    vi
    cv
    #
    cW
    cfv
    #
    @17
    c1
    caddc
    co
    #
    cW
    cfv
    #
    cpr
    #
    cG
    cedg
    cfv
    #
    wcel
    #
    vi
    cc0
    @5
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    w3a
    #
    @7
    @0
    @10
    wi
    vi
    @22
    cG
    @14
    cW
    @14
    eqid
    #
    @22
    eqid
    #
    iswwlks
    @0
    @27
    @7
    wa
    #
    @10
    @0
    @30
    wa
    #
    @10
    @9
    @3
    wcel
    #
    @9
    chash
    cfv
    #
    @1
    wceq
    #
    @31
    @9
    c0
    wne
    #
    @9
    @15
    wcel
    #
    @17
    @9
    cfv
    #
    @19
    @9
    cfv
    #
    cpr
    #
    @22
    wcel
    #
    vi
    cc0
    @33
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    @32
    @30
    @0
    @35
    @27
    @7
    @0
    @35
    wi
    #
    @16
    @13
    @7
    @44
    wi
    @26
    @16
    @7
    @0
    @35
    @16
    @7
    @0
    w3a
    #
    @16
    @1
    cn
    wcel
    #
    @1
    @5
    cle
    wbr
    #
    @35
    @16
    @7
    @0
    simp1
    @0
    @16
    @46
    @7
    cN
    nn0p1nn
    3ad2ant3
    @45
    @47
    @1
    @6
    cle
    wbr
    #
    @0
    @16
    @48
    @7
    @0
    @1
    @0
    @1
    @12
    nn0red
    lep1d
    #
    3ad2ant3
    @7
    @16
    @47
    @48
    wb
    @0
    @5
    @6
    @1
    cle
    breq2
    3ad2ant2
    mpbird
    @1
    @14
    cW
    swrdn0
    syl3anc
    3exp
    3ad2ant2
    imp
    impcom
    @30
    @36
    @0
    @27
    @36
    @7
    @16
    @13
    @36
    @26
    @14
    cW
    cc0
    @1
    swrdcl
    3ad2ant2
    adantr
    adantl
    @30
    @0
    @43
    @27
    @7
    @0
    @43
    @16
    @26
    @7
    @0
    wa
    #
    @43
    wi
    #
    @13
    @16
    @26
    @51
    @16
    @50
    @26
    @43
    @16
    @50
    @26
    @43
    @16
    @50
    wa
    #
    @26
    wa
    #
    @43
    @40
    vi
    cc0
    @1
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    @53
    @56
    @40
    vi
    cc0
    cN
    cfzo
    co
    #
    wral
    #
    @52
    @26
    @58
    @52
    @26
    @23
    vi
    cc0
    @1
    cfzo
    co
    #
    wral
    #
    @58
    @50
    @26
    @60
    wb
    @16
    @50
    @23
    vi
    @25
    @59
    @50
    @24
    @1
    cc0
    cfzo
    @7
    @0
    @24
    @6
    c1
    cmin
    co
    @1
    @5
    @6
    c1
    cmin
    oveq1
    @0
    @1
    c1
    @0
    @1
    @12
    nn0cnd
    @0
    1cnd
    #
    pncand
    sylan9eq
    oveq2d
    raleqdv
    adantl
    @52
    @60
    @23
    vi
    @57
    wral
    #
    @58
    @52
    @57
    @59
    wss
    #
    @60
    @62
    wi
    @52
    @1
    cN
    cuz
    cfv
    wcel
    #
    @63
    @52
    cN
    cz
    wcel
    #
    @1
    cz
    wcel
    #
    cN
    @1
    cle
    wbr
    #
    w3a
    #
    @64
    @0
    @68
    @16
    @7
    @0
    @65
    @66
    @67
    cN
    nn0z
    #
    @0
    @11
    @66
    @12
    @1
    nn0z
    syl
    @0
    cN
    cN
    nn0re
    lep1d
    3jca
    ad2antll
    cN
    @1
    eluz2
    sylibr
    cN
    cc0
    @1
    fzoss2
    syl
    @23
    vi
    @57
    @59
    ssralv
    syl
    @52
    @23
    @40
    vi
    @57
    @52
    @17
    @57
    wcel
    #
    wa
    #
    @23
    @40
    @71
    @21
    @39
    @22
    @71
    @18
    @37
    @20
    @38
    @71
    @37
    @18
    @71
    @16
    @1
    cc0
    @5
    cfz
    co
    #
    wcel
    #
    @17
    @59
    wcel
    #
    @37
    @18
    wceq
    @52
    @16
    @70
    @16
    @50
    simpl
    #
    adantr
    #
    @52
    @73
    @70
    @52
    @73
    @1
    cc0
    @6
    cfz
    co
    #
    wcel
    #
    @52
    @1
    cc0
    @1
    cfz
    co
    wcel
    #
    @78
    @0
    @79
    @16
    @7
    @0
    @11
    @79
    @12
    @1
    nn0fz0
    sylib
    ad2antll
    @1
    cc0
    @1
    fzelp1
    syl
    @50
    @73
    @78
    wb
    #
    @16
    @7
    @80
    @0
    @7
    @72
    @77
    @1
    @5
    @6
    cc0
    cfz
    oveq2
    eleq2d
    adantr
    #
    adantl
    mpbird
    adantr
    #
    @52
    @70
    @74
    @0
    @70
    @74
    wi
    @16
    @7
    @0
    @57
    @59
    @17
    cN
    fzossfzop1
    sseld
    ad2antll
    imp
    @17
    @1
    @14
    cW
    swrd0fv
    syl3anc
    eqcomd
    @71
    @38
    @20
    @71
    @16
    @73
    @19
    @59
    wcel
    #
    @38
    @20
    wceq
    @76
    @82
    @71
    @83
    @19
    cc0
    cN
    cfz
    co
    #
    wcel
    #
    @70
    @85
    @52
    cc0
    cN
    @17
    fzofzp1
    adantl
    @52
    @83
    @85
    wb
    #
    @70
    @0
    @86
    @16
    @7
    @0
    @59
    @84
    @19
    @0
    @65
    @59
    @84
    wceq
    @69
    @65
    @84
    @59
    cc0
    cN
    fzval3
    eqcomd
    syl
    eleq2d
    ad2antll
    adantr
    mpbird
    @19
    @1
    @14
    cW
    swrd0fv
    syl3anc
    eqcomd
    preq12d
    eleq1d
    biimpd
    ralimdva
    syld
    sylbid
    imp
    @53
    @40
    vi
    @55
    @57
    @52
    @55
    @57
    wceq
    #
    @26
    @0
    @87
    @16
    @7
    @0
    @54
    cN
    cc0
    cfzo
    @0
    cN
    c1
    cN
    nn0cn
    @61
    pncand
    oveq2d
    ad2antll
    adantr
    raleqdv
    mpbird
    @52
    @43
    @56
    wb
    @26
    @52
    @40
    vi
    @42
    @55
    @52
    @41
    @54
    cc0
    cfzo
    @52
    @33
    @1
    c1
    cmin
    @52
    @16
    @11
    @7
    @34
    @75
    @0
    @11
    @16
    @7
    @12
    ad2antll
    @50
    @7
    @16
    @7
    @0
    simpl
    adantl
    @1
    @14
    cW
    swrd0len0
    syl3anc
    oveq1d
    oveq2d
    raleqdv
    adantr
    mpbird
    exp31
    com23
    imp
    3adant1
    expdimp
    impcom
    vi
    @22
    cG
    @14
    @9
    @28
    @29
    iswwlks
    syl3anbrc
    @31
    @16
    @73
    wa
    #
    @34
    @30
    @0
    @88
    @27
    @7
    @0
    @88
    wi
    #
    @16
    @13
    @7
    @89
    wi
    @26
    @16
    @7
    @0
    @88
    @50
    @73
    @16
    @50
    @73
    @78
    @0
    @78
    @7
    @0
    @11
    @6
    cn0
    wcel
    #
    @48
    @78
    @12
    @0
    @11
    @90
    @12
    @1
    peano2nn0
    syl
    @49
    @1
    @6
    elfz2nn0
    syl3anbrc
    adantl
    @81
    mpbird
    anim2i
    exp32
    3ad2ant2
    imp
    impcom
    @14
    cW
    @1
    swrd0len
    syl
    @0
    @10
    @32
    @34
    wa
    wb
    @30
    cG
    cN
    @9
    iswwlksn
    adantr
    mpbir2and
    expcom
    sylanb
    com12
    sylbid
end
