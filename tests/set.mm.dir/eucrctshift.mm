include "ceupth.mm"
include "cfv.mm"
include "wbr.mm"
include "ccrcts.mm"
include "ctrls.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "cdm.mm"
include "wfo.mm"
include "wa.mm"
include "crctcshtrl.mm"
include "simpr.mm"
include "wf1o.mm"
include "eupthf1o.mm"
include "syl.mm"
include "adantr.mm"
include "wi.mm"
include "wf.mm"
include "cwlks.mm"
include "cword.mm"
include "wcel.mm"
include "trliswlk.mm"
include "wlkf.mm"
include "wrdf.mm"
include "3syl.mm"
include "wf1.mm"
include "df-f1o.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "dffo3.mm"
include "ccsh.mm"
include "caddc.mm"
include "cmo.mm"
include "crctiswlk.mm"
include "cn0.mm"
include "lencl.mm"
include "oveq2i.mm"
include "eleq2i.mm"
include "cle.mm"
include "cmin.mm"
include "cn.mm"
include "clt.mm"
include "wb.mm"
include "elfzonn0.mm"
include "adantl.mm"
include "nn0sub.mm"
include "syl2an.mm"
include "biimpac.mm"
include "w3a.mm"
include "elfzo0.mm"
include "simp2.mm"
include "sylbi.mm"
include "ad2antll.mm"
include "cr.mm"
include "nn0re.mm"
include "ad2antrr.mm"
include "nnre.mm"
include "elfzoelz.mm"
include "zred.mm"
include "readdcl.mm"
include "3jca.mm"
include "elfzole1.mm"
include "addge01.mm"
include "mpbid.mm"
include "lelttrdi.mm"
include "ex.mm"
include "com23.mm"
include "3impia.mm"
include "adantld.mm"
include "imp.mm"
include "3ad2ant1.mm"
include "elfzoel2.mm"
include "ltsubaddd.mm"
include "mpbird.mm"
include "impcom.mm"
include "syl3anbrc.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "cc.mm"
include "zcnd.mm"
include "anim12ci.mm"
include "npcan.mm"
include "zmodidfzoimp.mm"
include "eqtrd.mm"
include "sylan9eqr.mm"
include "eqcomd.mm"
include "rspcedeq2vd.mm"
include "wn.mm"
include "nn0cn.mm"
include "nncn.mm"
include "3ad2ant2.mm"
include "subadd23d.mm"
include "simpll.mm"
include "cz.mm"
include "nn0z.mm"
include "nnz.mm"
include "znnsub.mm"
include "biimp3a.mm"
include "nnnn0d.mm"
include "nn0addcld.mm"
include "eqeltrd.mm"
include "simplr2.mm"
include "subcl.mm"
include "jca.mm"
include "addcom.mm"
include "ltnle.mm"
include "simpl.mm"
include "sublt0d.mm"
include "biimprd.mm"
include "sylbird.mm"
include "resubcl.mm"
include "ltaddneg.mm"
include "eqbrtrrd.mm"
include "exp31.mm"
include "3adant2.mm"
include "syl5bi.mm"
include "sylibr.mm"
include "simp3.mm"
include "simp1.mm"
include "nppcand.mm"
include "comraddd.mm"
include "biimpi.mm"
include "addmodid.mm"
include "pm2.61ian.mm"
include "rexeqi.mm"
include "sylc.mm"
include "fveq2.mm"
include "reximi.mm"
include "ad3antrrr.mm"
include "cshwidxmod.mm"
include "syl2an3an.mm"
include "eqeq2d.mm"
include "rexbidva.mm"
include "crctcshlem2.mm"
include "oveq2d.mm"
include "fveq1i.mm"
include "a1i.mm"
include "eqeq12d.mm"
include "rexeqbidv.mm"
include "rexlimdva.mm"
include "ralimdva.mm"
include "anim1i.mm"
include "ancomd.mm"
include "simplbiim.mm"
include "com13.mm"
include "mpd.mm"
include "mpdan.mm"
include "iseupth.mm"
include "crctcsh.mm"

theorem eucrctshift
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N
  let cV: class V
  let vi: setvar i
  let vy: setvar y
  let vz: setvar z
  assume eucrctshift.v: |- V = ( Vtx ` G )
  assume eucrctshift.i: |- I = ( iEdg ` G )
  assume eucrctshift.c: |- ( ph -> F ( Circuits ` G ) P )
  assume eucrctshift.n: |- N = ( # ` F )
  assume eucrctshift.s: |- ( ph -> S e. ( 0 ..^ N ) )
  assume eucrctshift.h: |- H = ( F cyclShift S )
  assume eucrctshift.q: |- Q = ( x e. ( 0 ... N ) |-> if ( x <_ ( N - S ) , ( P ` ( x + S ) ) , ( P ` ( ( x + S ) - N ) ) ) )
  assume eucrctshift.e: |- ( ph -> F ( EulerPaths ` G ) P )

  disjoint F x
  disjoint H x
  disjoint I x
  disjoint N x
  disjoint P x
  disjoint S x
  disjoint V x
  disjoint ph x
  disjoint F i
  disjoint F y
  disjoint F z
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint H i
  disjoint H y
  disjoint H z
  disjoint I i
  disjoint I y
  disjoint I z
  disjoint N z
  disjoint S y
  disjoint S z
  disjoint i ph
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( H ( EulerPaths ` G ) Q /\ H ( Circuits ` G ) Q ) )

  proof
    wph
    cH
    cQ
    cG
    ceupth
    cfv
    #
    wbr
    #
    cH
    cQ
    cG
    ccrcts
    cfv
    #
    wbr
    wph
    cH
    cQ
    cG
    ctrls
    cfv
    wbr
    #
    cc0
    cH
    chash
    cfv
    #
    cfzo
    co
    #
    cI
    cdm
    #
    cH
    wfo
    #
    wa
    #
    @1
    wph
    @3
    @8
    wph
    vx
    cP
    cQ
    cS
    cF
    cG
    cH
    cI
    cN
    cV
    eucrctshift.v
    eucrctshift.i
    eucrctshift.c
    eucrctshift.n
    eucrctshift.s
    eucrctshift.h
    eucrctshift.q
    crctcshtrl
    wph
    @3
    wa
    #
    @3
    @7
    wph
    @3
    simpr
    @9
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    @6
    cF
    wf1o
    #
    @7
    wph
    @12
    @3
    wph
    cF
    cP
    @0
    wbr
    @12
    eucrctshift.e
    cP
    cF
    cG
    cI
    eucrctshift.i
    eupthf1o
    syl
    adantr
    @3
    wph
    @12
    @7
    wi
    #
    @3
    @5
    @6
    cH
    wf
    #
    wph
    @13
    wi
    @3
    cH
    cQ
    cG
    cwlks
    cfv
    #
    wbr
    cH
    @6
    cword
    #
    wcel
    @14
    cQ
    cH
    cG
    trliswlk
    cQ
    cH
    cG
    cI
    eucrctshift.i
    wlkf
    @6
    cH
    wrdf
    3syl
    @12
    wph
    @14
    @7
    @12
    @11
    @6
    cF
    wf1
    @11
    @6
    cF
    wfo
    #
    wph
    @14
    @7
    wi
    wi
    #
    @11
    @6
    cF
    df-f1o
    @17
    @11
    @6
    cF
    wf
    vi
    cv
    #
    vy
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vy
    @11
    wrex
    #
    vi
    @6
    wral
    #
    @18
    vy
    vi
    @11
    @6
    cF
    dffo3
    @24
    wph
    @14
    @7
    @24
    wph
    wa
    #
    @14
    wa
    #
    @14
    @19
    vz
    cv
    #
    cH
    cfv
    #
    wceq
    #
    vz
    @5
    wrex
    #
    vi
    @6
    wral
    #
    wa
    @7
    @26
    @31
    @14
    @25
    @31
    @14
    wph
    @24
    @31
    wph
    @23
    @30
    vi
    @6
    wph
    @19
    @6
    wcel
    #
    wa
    #
    @22
    @30
    vy
    @11
    @33
    @20
    @11
    wcel
    #
    wa
    #
    @22
    @30
    @35
    @22
    wa
    #
    @30
    @21
    @27
    cF
    cS
    ccsh
    co
    #
    cfv
    #
    wceq
    #
    vz
    cc0
    cN
    cfzo
    co
    #
    wrex
    #
    @36
    @41
    @21
    @27
    cS
    caddc
    co
    #
    @10
    cmo
    co
    #
    cF
    cfv
    #
    wceq
    #
    vz
    @40
    wrex
    #
    @36
    @20
    @43
    wceq
    #
    vz
    @40
    wrex
    #
    @46
    @35
    @48
    @22
    @33
    @34
    @48
    wph
    @34
    @48
    wi
    #
    @32
    wph
    cF
    cP
    @2
    wbr
    #
    cS
    @40
    wcel
    #
    @49
    eucrctshift.c
    eucrctshift.s
    @50
    cF
    cP
    @15
    wbr
    #
    cF
    @16
    wcel
    #
    @51
    @49
    wi
    #
    cP
    cF
    cG
    crctiswlk
    #
    cP
    cF
    cG
    cI
    eucrctshift.i
    wlkf
    #
    @53
    @10
    cn0
    wcel
    #
    @54
    @6
    cF
    lencl
    @51
    cS
    @11
    wcel
    #
    @57
    @49
    @40
    @11
    cS
    cN
    @10
    cc0
    cfzo
    eucrctshift.n
    oveq2i
    #
    eleq2i
    @57
    @58
    @34
    @48
    @57
    @58
    wa
    #
    @34
    wa
    #
    @47
    vz
    @11
    wrex
    #
    @48
    cS
    @20
    cle
    wbr
    #
    @61
    @62
    @63
    @61
    wa
    #
    vz
    @20
    cS
    cmin
    co
    #
    @11
    @20
    @43
    @64
    @65
    cn0
    wcel
    #
    @10
    cn
    wcel
    #
    @65
    @10
    clt
    wbr
    #
    @65
    @11
    wcel
    @61
    @63
    @66
    @60
    cS
    cn0
    wcel
    #
    @20
    cn0
    wcel
    #
    @63
    @66
    wb
    @34
    @58
    @69
    @57
    cS
    @10
    elfzonn0
    adantl
    @20
    @10
    elfzonn0
    cS
    @20
    nn0sub
    syl2an
    biimpac
    @34
    @67
    @63
    @60
    @34
    @70
    @67
    @20
    @10
    clt
    wbr
    #
    w3a
    #
    @67
    @20
    @10
    elfzo0
    #
    @70
    @67
    @71
    simp2
    sylbi
    ad2antll
    @61
    @68
    @63
    @34
    @60
    @68
    @34
    @72
    @60
    @68
    wi
    @73
    @72
    @60
    @68
    @72
    @60
    wa
    #
    @68
    @20
    @10
    cS
    caddc
    co
    #
    clt
    wbr
    #
    @72
    @60
    @76
    @72
    @58
    @76
    @57
    @70
    @67
    @71
    @58
    @76
    wi
    @70
    @67
    wa
    #
    @58
    @71
    @76
    @77
    @58
    @71
    @76
    wi
    @77
    @58
    wa
    #
    @20
    @10
    @75
    @78
    @20
    cr
    wcel
    #
    @10
    cr
    wcel
    #
    @75
    cr
    wcel
    #
    @70
    @79
    @67
    @58
    @20
    nn0re
    #
    ad2antrr
    @77
    @80
    @58
    @67
    @80
    @70
    @10
    nnre
    #
    adantl
    #
    adantr
    @77
    @80
    cS
    cr
    wcel
    #
    @81
    @58
    @84
    @58
    cS
    cS
    cc0
    @10
    elfzoelz
    #
    zred
    #
    @10
    cS
    readdcl
    syl2an
    3jca
    @78
    cc0
    cS
    cle
    wbr
    #
    @10
    @75
    cle
    wbr
    #
    @58
    @88
    @77
    cS
    cc0
    @10
    elfzole1
    adantl
    @77
    @80
    @85
    @88
    @89
    wb
    @58
    @84
    @87
    @10
    cS
    addge01
    syl2an
    mpbid
    lelttrdi
    ex
    com23
    3impia
    adantld
    imp
    @74
    @20
    cS
    @10
    @72
    @79
    @60
    @70
    @67
    @79
    @71
    @82
    3ad2ant1
    adantr
    @58
    @85
    @72
    @57
    @87
    ad2antll
    @58
    @80
    @72
    @57
    @58
    @10
    cS
    cc0
    @10
    elfzoel2
    zred
    ad2antll
    ltsubaddd
    mpbird
    ex
    sylbi
    impcom
    adantl
    @65
    @10
    elfzo0
    syl3anbrc
    @64
    @27
    @65
    wceq
    #
    wa
    @43
    @20
    @90
    @64
    @43
    @65
    cS
    caddc
    co
    #
    @10
    cmo
    co
    #
    @20
    @90
    @42
    @91
    @10
    cmo
    @27
    @65
    cS
    caddc
    oveq1
    oveq1d
    @64
    @92
    @20
    @10
    cmo
    co
    #
    @20
    @64
    @91
    @20
    @10
    cmo
    @64
    @20
    cc
    wcel
    #
    cS
    cc
    wcel
    #
    wa
    #
    @91
    @20
    wceq
    @61
    @96
    @63
    @60
    @95
    @34
    @94
    @58
    @95
    @57
    @58
    cS
    @86
    zcnd
    adantl
    #
    @34
    @20
    @20
    cc0
    @10
    elfzoelz
    zcnd
    #
    anim12ci
    adantl
    @20
    cS
    npcan
    syl
    oveq1d
    @34
    @93
    @20
    wceq
    @63
    @60
    @20
    @10
    zmodidfzoimp
    ad2antll
    eqtrd
    sylan9eqr
    eqcomd
    rspcedeq2vd
    @63
    wn
    #
    @61
    wa
    #
    vz
    @65
    @10
    caddc
    co
    #
    @11
    @20
    @43
    @100
    @101
    cn0
    wcel
    #
    @67
    @101
    @10
    clt
    wbr
    #
    w3a
    #
    @101
    @11
    wcel
    @61
    @99
    @104
    @34
    @60
    @99
    @104
    wi
    #
    @34
    @72
    @60
    @105
    wi
    @73
    @72
    @58
    @105
    @57
    @58
    @69
    @67
    cS
    @10
    clt
    wbr
    #
    w3a
    #
    @72
    @105
    cS
    @10
    elfzo0
    @70
    @71
    @107
    @105
    wi
    @67
    @70
    @71
    wa
    #
    @107
    @99
    @104
    @108
    @107
    wa
    #
    @99
    wa
    #
    @102
    @67
    @103
    @109
    @102
    @99
    @109
    @101
    @20
    @10
    cS
    cmin
    co
    #
    caddc
    co
    cn0
    @109
    @20
    cS
    @10
    @70
    @94
    @71
    @107
    @20
    nn0cn
    #
    ad2antrr
    @107
    @95
    @108
    @69
    @67
    @95
    @106
    cS
    nn0cn
    3ad2ant1
    #
    adantl
    @107
    @10
    cc
    wcel
    #
    @108
    @67
    @69
    @114
    @106
    @10
    nncn
    3ad2ant2
    adantl
    #
    subadd23d
    @109
    @20
    @111
    @70
    @71
    @107
    simpll
    @109
    @111
    @107
    @111
    cn
    wcel
    #
    @108
    @69
    @67
    @106
    @116
    @69
    cS
    cz
    wcel
    #
    @10
    cz
    wcel
    @106
    @116
    wb
    @67
    cS
    nn0z
    @10
    nnz
    cS
    @10
    znnsub
    syl2an
    biimp3a
    adantl
    nnnn0d
    nn0addcld
    eqeltrd
    adantr
    @69
    @67
    @106
    @108
    @99
    simplr2
    @110
    @10
    @65
    caddc
    co
    #
    @101
    @10
    clt
    @110
    @114
    @65
    cc
    wcel
    #
    wa
    #
    @118
    @101
    wceq
    @109
    @120
    @99
    @109
    @114
    @119
    @115
    @108
    @94
    @95
    @119
    @107
    @70
    @94
    @71
    @112
    adantr
    @113
    @20
    cS
    subcl
    syl2an
    jca
    adantr
    @10
    @65
    addcom
    syl
    @110
    @65
    cc0
    clt
    wbr
    #
    @118
    @10
    clt
    wbr
    #
    @109
    @99
    @121
    @108
    @79
    @85
    @99
    @121
    wi
    @107
    @70
    @79
    @71
    @82
    adantr
    #
    @69
    @67
    @85
    @106
    cS
    nn0re
    3ad2ant1
    #
    @79
    @85
    wa
    #
    @99
    @20
    cS
    clt
    wbr
    #
    @121
    @20
    cS
    ltnle
    @125
    @121
    @126
    @125
    @20
    cS
    @79
    @85
    simpl
    @79
    @85
    simpr
    sublt0d
    biimprd
    sylbird
    syl2an
    imp
    @110
    @65
    cr
    wcel
    #
    @80
    wa
    #
    @121
    @122
    wb
    @109
    @128
    @99
    @109
    @127
    @80
    @108
    @79
    @85
    @127
    @107
    @123
    @124
    @20
    cS
    resubcl
    syl2an
    @107
    @80
    @108
    @67
    @69
    @80
    @106
    @83
    3ad2ant2
    adantl
    jca
    adantr
    @65
    @10
    ltaddneg
    syl
    mpbid
    eqbrtrrd
    3jca
    exp31
    3adant2
    syl5bi
    adantld
    sylbi
    impcom
    impcom
    @101
    @10
    elfzo0
    sylibr
    @100
    @27
    @101
    wceq
    #
    wa
    @43
    @20
    @129
    @100
    @43
    @101
    cS
    caddc
    co
    #
    @10
    cmo
    co
    #
    @20
    @129
    @42
    @130
    @10
    cmo
    @27
    @101
    cS
    caddc
    oveq1
    oveq1d
    @100
    @131
    @10
    @20
    caddc
    co
    #
    @10
    cmo
    co
    #
    @20
    @100
    @130
    @132
    @10
    cmo
    @100
    @95
    @94
    @114
    w3a
    #
    @130
    @132
    wceq
    @61
    @134
    @99
    @61
    @95
    @94
    @114
    @60
    @95
    @34
    @97
    adantr
    @34
    @94
    @60
    @98
    adantl
    @57
    @114
    @58
    @34
    @10
    nn0cn
    ad2antrr
    3jca
    adantl
    @134
    @130
    @20
    @10
    @95
    @94
    @114
    simp2
    #
    @95
    @94
    @114
    simp3
    #
    @134
    @20
    cS
    @10
    @135
    @95
    @94
    @114
    simp1
    @136
    nppcand
    comraddd
    syl
    oveq1d
    @100
    @72
    @133
    @20
    wceq
    @34
    @72
    @99
    @60
    @34
    @72
    @73
    biimpi
    ad2antll
    @20
    @10
    addmodid
    syl
    eqtrd
    sylan9eqr
    eqcomd
    rspcedeq2vd
    pm2.61ian
    @47
    vz
    @40
    @11
    @59
    rexeqi
    sylibr
    exp31
    syl5bi
    syl
    3syl
    sylc
    adantr
    imp
    adantr
    @47
    @45
    vz
    @40
    @20
    @43
    cF
    fveq2
    reximi
    syl
    @36
    @39
    @45
    vz
    @40
    @36
    @27
    @40
    wcel
    #
    wa
    @38
    @44
    @21
    @36
    @53
    @117
    @137
    @27
    @11
    wcel
    #
    @38
    @44
    wceq
    wph
    @53
    @32
    @34
    @22
    wph
    @50
    @52
    @53
    eucrctshift.c
    @55
    @56
    3syl
    ad3antrrr
    wph
    @117
    @32
    @34
    @22
    wph
    @51
    @117
    eucrctshift.s
    cS
    cc0
    cN
    elfzoelz
    syl
    ad3antrrr
    @137
    @138
    @40
    @11
    @27
    @59
    eleq2i
    biimpi
    @27
    cS
    @6
    cF
    cshwidxmod
    syl2an3an
    eqeq2d
    rexbidva
    mpbird
    @36
    @29
    @39
    vz
    @5
    @40
    wph
    @5
    @40
    wceq
    @32
    @34
    @22
    wph
    @4
    cN
    cc0
    cfzo
    wph
    cP
    cS
    cF
    cG
    cH
    cI
    cN
    cV
    eucrctshift.v
    eucrctshift.i
    eucrctshift.c
    eucrctshift.n
    eucrctshift.s
    eucrctshift.h
    crctcshlem2
    oveq2d
    ad3antrrr
    @36
    @19
    @21
    @28
    @38
    @35
    @22
    simpr
    @28
    @38
    wceq
    @36
    @27
    cH
    @37
    eucrctshift.h
    fveq1i
    a1i
    eqeq12d
    rexeqbidv
    mpbird
    ex
    rexlimdva
    ralimdva
    impcom
    anim1i
    ancomd
    vz
    vi
    @5
    @6
    cH
    dffo3
    sylibr
    exp31
    simplbiim
    simplbiim
    com13
    syl
    impcom
    mpd
    jca
    mpdan
    cQ
    cH
    cG
    cI
    eucrctshift.i
    iseupth
    sylibr
    wph
    vx
    cP
    cQ
    cS
    cF
    cG
    cH
    cI
    cN
    cV
    eucrctshift.v
    eucrctshift.i
    eucrctshift.c
    eucrctshift.n
    eucrctshift.s
    eucrctshift.h
    eucrctshift.q
    crctcsh
    jca
end
