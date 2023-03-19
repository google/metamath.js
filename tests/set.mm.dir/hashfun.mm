include "cfn.mm"
include "wcel.mm"
include "wfun.mm"
include "chash.mm"
include "cfv.mm"
include "cdm.mm"
include "wceq.mm"
include "wfn.mm"
include "funfn.mm"
include "hashfn.mm"
include "sylbi.mm"
include "wa.mm"
include "wrel.mm"
include "cv.mm"
include "cop.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wn.mm"
include "wne.mm"
include "cr.mm"
include "cn0.mm"
include "dmfi.mm"
include "hashcl.mm"
include "syl.mm"
include "nn0red.mm"
include "adantr.mm"
include "clt.mm"
include "wbr.mm"
include "cvv.mm"
include "cxp.mm"
include "wrex.mm"
include "wral.mm"
include "wss.mm"
include "df-rel.mm"
include "dfss3.mm"
include "bitri.mm"
include "notbii.mm"
include "rexnal.mm"
include "bitr4i.mm"
include "w3a.mm"
include "csn.mm"
include "cdif.mm"
include "cun.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "dmun.mm"
include "fveq2i.mm"
include "c0.mm"
include "dmsnn0.mm"
include "biimpri.mm"
include "necon1bi.mm"
include "3ad2ant3.mm"
include "uneq2d.mm"
include "un0.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "diffi.mm"
include "peano2re.mm"
include "cle.mm"
include "cdom.mm"
include "fidomdm.mm"
include "wb.mm"
include "hashdom.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "ltp1d.mm"
include "lelttrd.mm"
include "3ad2ant1.mm"
include "eqbrtrd.mm"
include "cin.mm"
include "snfi.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "hashun.mm"
include "mp3an23.mm"
include "vex.mm"
include "hashsng.mm"
include "ax-mp.mm"
include "oveq2i.mm"
include "syl6req.mm"
include "breqtrd.mm"
include "difsnid.mm"
include "dmeqd.mm"
include "3ad2ant2.mm"
include "3brtr3d.mm"
include "rexlimdv3a.mm"
include "syl5bi.mm"
include "imp.mm"
include "gtned.mm"
include "ex.mm"
include "necon4bd.mm"
include "wex.mm"
include "2nalexn.mm"
include "df-ne.mm"
include "anbi2i.mm"
include "annim.mm"
include "exbii.mm"
include "exnal.mm"
include "bitr2i.mm"
include "2exbii.mm"
include "c2.mm"
include "cpr.mm"
include "2re.mm"
include "readdcl.mm"
include "sylancr.mm"
include "1re.mm"
include "opex.mm"
include "prss.mm"
include "undif.mm"
include "sylbb.mm"
include "syl5reqr.mm"
include "dmprop.mm"
include "dfsn2.mm"
include "eqtr4i.mm"
include "uneq1i.mm"
include "ad2antrl.mm"
include "hashun2.mm"
include "oveq1i.mm"
include "syl6breq.mm"
include "1lt2.mm"
include "ltadd1.mm"
include "mp3an12i.mm"
include "mpbii.mm"
include "leadd2.mm"
include "mp3an3.mm"
include "mpbid.mm"
include "prfi.mm"
include "mp3an13.mm"
include "opth.mm"
include "simprbi.mm"
include "necon3i.mm"
include "hashprg.mm"
include "mp2an.mm"
include "sylib.mm"
include "oveq1d.mm"
include "ad2antll.mm"
include "3eqtr3rd.mm"
include "ltletrd.mm"
include "exlimdv.mm"
include "exlimdvv.mm"
include "dffun4.mm"
include "sylanbrc.mm"
include "impbid2.mm"

theorem hashfun
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( F e. Fin -> ( Fun F <-> ( # ` F ) = ( # ` dom F ) ) )

  proof
    cF
    cfn
    wcel
    #
    cF
    wfun
    #
    cF
    chash
    cfv
    #
    cF
    cdm
    #
    chash
    cfv
    #
    wceq
    #
    @1
    cF
    @3
    wfn
    @5
    cF
    funfn
    @3
    cF
    hashfn
    sylbi
    @0
    @5
    @1
    @0
    @5
    wa
    cF
    wrel
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cF
    wcel
    @7
    vz
    cv
    #
    cop
    #
    cF
    wcel
    wa
    #
    vy
    vz
    weq
    #
    wi
    #
    vz
    wal
    #
    vy
    wal
    vx
    wal
    #
    @1
    @0
    @5
    @6
    @0
    @6
    @2
    @4
    @0
    @6
    wn
    #
    @2
    @4
    wne
    #
    @0
    @17
    wa
    @4
    @2
    @0
    @4
    cr
    wcel
    #
    @17
    @0
    @4
    @0
    @3
    cfn
    wcel
    @4
    cn0
    wcel
    cF
    dmfi
    @3
    hashcl
    syl
    nn0red
    #
    adantr
    @0
    @17
    @4
    @2
    clt
    wbr
    #
    @17
    @7
    cvv
    cvv
    cxp
    #
    wcel
    #
    wn
    #
    vx
    cF
    wrex
    #
    @0
    @21
    @17
    @23
    vx
    cF
    wral
    #
    wn
    @25
    @6
    @26
    @6
    cF
    @22
    wss
    @26
    cF
    df-rel
    vx
    cF
    @22
    dfss3
    bitri
    notbii
    @23
    vx
    cF
    rexnal
    bitr4i
    @0
    @24
    @21
    vx
    cF
    @0
    @7
    cF
    wcel
    #
    @24
    w3a
    #
    cF
    @7
    csn
    #
    cdif
    #
    @29
    cun
    #
    cdm
    #
    chash
    cfv
    #
    @31
    chash
    cfv
    #
    @4
    @2
    clt
    @28
    @33
    @30
    chash
    cfv
    #
    c1
    caddc
    co
    #
    @34
    clt
    @28
    @33
    @30
    cdm
    #
    chash
    cfv
    #
    @36
    clt
    @28
    @33
    @37
    @29
    cdm
    #
    cun
    #
    chash
    cfv
    @38
    @32
    @40
    chash
    @30
    @29
    dmun
    fveq2i
    @28
    @40
    @37
    chash
    @28
    @40
    @37
    c0
    cun
    @37
    @28
    @39
    c0
    @37
    @24
    @0
    @39
    c0
    wceq
    @27
    @23
    @39
    c0
    @23
    @39
    c0
    wne
    @7
    dmsnn0
    biimpri
    necon1bi
    3ad2ant3
    uneq2d
    @37
    un0
    syl6eq
    fveq2d
    syl5eq
    @0
    @27
    @38
    @36
    clt
    wbr
    @24
    @0
    @38
    @35
    @36
    @0
    @38
    @0
    @37
    cfn
    wcel
    #
    @38
    cn0
    wcel
    @0
    @30
    cfn
    wcel
    #
    @41
    cF
    @29
    diffi
    #
    @30
    dmfi
    syl
    #
    @37
    hashcl
    syl
    nn0red
    @0
    @35
    @0
    @42
    @35
    cn0
    wcel
    @43
    @30
    hashcl
    syl
    nn0red
    #
    @0
    @35
    cr
    wcel
    @36
    cr
    wcel
    @45
    @35
    peano2re
    syl
    @0
    @38
    @35
    cle
    wbr
    #
    @37
    @30
    cdom
    wbr
    #
    @0
    @42
    @47
    @43
    @30
    fidomdm
    syl
    @0
    @41
    @42
    @46
    @47
    wb
    @44
    @43
    @37
    @30
    cfn
    hashdom
    syl2anc
    mpbird
    @0
    @35
    @45
    ltp1d
    lelttrd
    3ad2ant1
    eqbrtrd
    @0
    @27
    @36
    @34
    wceq
    @24
    @0
    @34
    @35
    @29
    chash
    cfv
    #
    caddc
    co
    #
    @36
    @0
    @42
    @34
    @49
    wceq
    #
    @43
    @42
    @29
    cfn
    wcel
    #
    @30
    @29
    cin
    #
    c0
    wceq
    @50
    @7
    snfi
    #
    @52
    @29
    @30
    cin
    c0
    @30
    @29
    incom
    @29
    cF
    disjdif
    eqtri
    @30
    @29
    hashun
    mp3an23
    syl
    @48
    c1
    @35
    caddc
    @7
    cvv
    wcel
    @48
    c1
    wceq
    vx
    vex
    #
    @7
    cvv
    hashsng
    ax-mp
    #
    oveq2i
    syl6req
    3ad2ant1
    breqtrd
    @27
    @0
    @33
    @4
    wceq
    @24
    @27
    @32
    @3
    chash
    @27
    @31
    cF
    cF
    @7
    difsnid
    #
    dmeqd
    fveq2d
    3ad2ant2
    @27
    @0
    @34
    @2
    wceq
    @24
    @27
    @31
    cF
    chash
    @56
    fveq2d
    3ad2ant2
    3brtr3d
    rexlimdv3a
    syl5bi
    imp
    gtned
    ex
    necon4bd
    imp
    @0
    @5
    @16
    @0
    @16
    @2
    @4
    @16
    wn
    #
    @12
    @8
    @10
    wne
    #
    wa
    #
    vz
    wex
    #
    vy
    wex
    vx
    wex
    #
    @0
    @18
    @57
    @15
    wn
    #
    vy
    wex
    vx
    wex
    @61
    @15
    vx
    vy
    2nalexn
    @62
    @60
    vx
    vy
    @60
    @14
    wn
    #
    vz
    wex
    @62
    @59
    @63
    vz
    @59
    @12
    @13
    wn
    #
    wa
    @63
    @58
    @64
    @12
    @8
    @10
    df-ne
    anbi2i
    @12
    @13
    annim
    bitri
    exbii
    @14
    vz
    exnal
    bitr2i
    2exbii
    bitri
    @0
    @60
    @18
    vx
    vy
    @0
    @59
    @18
    vz
    @0
    @59
    @18
    @0
    @59
    wa
    #
    @4
    @2
    @0
    @19
    @59
    @20
    adantr
    #
    @65
    @4
    c2
    cF
    @9
    @11
    cpr
    #
    cdif
    #
    cdm
    #
    chash
    cfv
    #
    caddc
    co
    #
    @2
    @66
    @65
    c2
    cr
    wcel
    #
    @70
    cr
    wcel
    #
    @71
    cr
    wcel
    #
    2re
    @0
    @73
    @59
    @0
    @70
    @0
    @69
    cfn
    wcel
    #
    @70
    cn0
    wcel
    @0
    @68
    cfn
    wcel
    #
    @75
    cF
    @67
    diffi
    #
    @68
    dmfi
    syl
    #
    @69
    hashcl
    syl
    nn0red
    #
    adantr
    c2
    @70
    readdcl
    #
    sylancr
    @0
    @2
    cr
    wcel
    @59
    @0
    @2
    cF
    hashcl
    nn0red
    adantr
    @65
    @4
    c1
    @70
    caddc
    co
    #
    @71
    @66
    @0
    @81
    cr
    wcel
    #
    @59
    @0
    c1
    cr
    wcel
    #
    @73
    @82
    1re
    @79
    c1
    @70
    readdcl
    sylancr
    adantr
    @0
    @74
    @59
    @0
    @72
    @73
    @74
    2re
    @79
    @80
    sylancr
    adantr
    @65
    @4
    @29
    @69
    cun
    #
    chash
    cfv
    #
    @81
    cle
    @12
    @4
    @85
    wceq
    @0
    @58
    @12
    @3
    @84
    chash
    @12
    @3
    @67
    cdm
    #
    @69
    cun
    #
    @84
    @12
    @87
    @67
    @68
    cun
    #
    cdm
    @3
    @67
    @68
    dmun
    @12
    @88
    cF
    @12
    @67
    cF
    wss
    @88
    cF
    wceq
    @9
    @11
    cF
    @7
    @8
    opex
    #
    @7
    @10
    opex
    #
    prss
    @67
    cF
    undif
    sylbb
    #
    dmeqd
    syl5reqr
    @86
    @29
    @69
    @86
    @7
    @7
    cpr
    @29
    @7
    @8
    @7
    @10
    vy
    vex
    #
    vz
    vex
    dmprop
    @7
    dfsn2
    eqtr4i
    uneq1i
    syl6eq
    fveq2d
    ad2antrl
    @0
    @85
    @81
    cle
    wbr
    @59
    @0
    @85
    @48
    @70
    caddc
    co
    #
    @81
    cle
    @0
    @51
    @75
    @85
    @93
    cle
    wbr
    @53
    @78
    @29
    @69
    hashun2
    sylancr
    @48
    c1
    @70
    caddc
    @55
    oveq1i
    syl6breq
    adantr
    eqbrtrd
    @0
    @81
    @71
    clt
    wbr
    #
    @59
    @0
    c1
    c2
    clt
    wbr
    #
    @94
    1lt2
    @83
    @72
    @0
    @73
    @95
    @94
    wb
    1re
    2re
    @79
    c1
    c2
    @70
    ltadd1
    mp3an12i
    mpbii
    adantr
    lelttrd
    @65
    @71
    c2
    @68
    chash
    cfv
    #
    caddc
    co
    #
    @2
    cle
    @0
    @71
    @97
    cle
    wbr
    #
    @59
    @0
    @70
    @96
    cle
    wbr
    #
    @98
    @0
    @99
    @69
    @68
    cdom
    wbr
    #
    @0
    @76
    @100
    @77
    @68
    fidomdm
    syl
    @0
    @75
    @76
    @99
    @100
    wb
    @78
    @77
    @69
    @68
    cfn
    hashdom
    syl2anc
    mpbird
    @0
    @73
    @96
    cr
    wcel
    #
    @99
    @98
    wb
    #
    @79
    @0
    @96
    @0
    @76
    @96
    cn0
    wcel
    @77
    @68
    hashcl
    syl
    nn0red
    @73
    @101
    @72
    @102
    2re
    @70
    @96
    c2
    leadd2
    mp3an3
    syl2anc
    mpbid
    adantr
    @65
    @88
    chash
    cfv
    #
    @67
    chash
    cfv
    #
    @96
    caddc
    co
    #
    @2
    @97
    @0
    @103
    @105
    wceq
    #
    @59
    @0
    @76
    @106
    @77
    @67
    cfn
    wcel
    @76
    @67
    @68
    cin
    c0
    wceq
    @106
    @9
    @11
    prfi
    @67
    cF
    disjdif
    @67
    @68
    hashun
    mp3an13
    syl
    adantr
    @12
    @103
    @2
    wceq
    @0
    @58
    @12
    @88
    cF
    chash
    @91
    fveq2d
    ad2antrl
    @58
    @105
    @97
    wceq
    @0
    @12
    @58
    @104
    c2
    @96
    caddc
    @58
    @9
    @11
    wne
    #
    @104
    c2
    wceq
    #
    @9
    @11
    @8
    @10
    @9
    @11
    wceq
    vx
    vx
    weq
    @13
    @7
    @8
    @7
    @10
    @54
    @92
    opth
    simprbi
    necon3i
    @9
    cvv
    wcel
    @11
    cvv
    wcel
    @107
    @108
    wb
    @89
    @90
    @9
    @11
    cvv
    cvv
    hashprg
    mp2an
    sylib
    oveq1d
    ad2antll
    3eqtr3rd
    breqtrd
    ltletrd
    gtned
    ex
    exlimdv
    exlimdvv
    syl5bi
    necon4bd
    imp
    vx
    vy
    vz
    cF
    dffun4
    sylanbrc
    ex
    impbid2
end
