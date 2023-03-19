include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "ciedg.mm"
include "cdm.mm"
include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "cvtx.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "wif.mm"
include "cfzo.mm"
include "wral.mm"
include "cres.mm"
include "wfn.mm"
include "wlkf.mm"
include "wrdfn.mm"
include "3syl.mm"
include "cuz.mm"
include "elfzouz2.mm"
include "fzoss2.mm"
include "fnssres.mm"
include "syl2anc.mm"
include "wa.mm"
include "cima.mm"
include "cin.mm"
include "wrex.mm"
include "simpr.mm"
include "wb.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "adantl.mm"
include "fvres.mm"
include "eqcomd.mm"
include "rspcedvd.mm"
include "adantr.mm"
include "fvelimabd.mm"
include "mpbird.mm"
include "wi.mm"
include "syl.mm"
include "wrdf.mm"
include "ffvelrn.mm"
include "expcom.mm"
include "sselda.mm"
include "syl11.mm"
include "expd.mm"
include "mpcom.mm"
include "imp.mm"
include "eqeltrd.mm"
include "elind.mm"
include "dmres.mm"
include "syl6eleqr.mm"
include "dmeqd.mm"
include "eleq2d.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "fzossfz.mm"
include "sseldi.mm"
include "wlkreslem0.mm"
include "oveq2d.mm"
include "feq2d.mm"
include "iswrdb.mm"
include "sylibr.mm"
include "syl5eqel.mm"
include "wlkp.mm"
include "feq3d.mm"
include "elfzuz3.mm"
include "fzss2.mm"
include "fssresd.mm"
include "fveq2i.mm"
include "syl5eq.mm"
include "feq1i.mm"
include "w3a.mm"
include "cvv.mm"
include "wlkv.mm"
include "iswlk.mm"
include "biimpd.mm"
include "fveq1i.mm"
include "a1i.mm"
include "fvresd.mm"
include "syl5req.mm"
include "fzofzp1.mm"
include "jca.mm"
include "ex.mm"
include "sylbid.mm"
include "ancli.mm"
include "wfun.mm"
include "ffund.mm"
include "fdm.mm"
include "sseq2.mm"
include "syl5ibr.mm"
include "impcom.mm"
include "resfvresima.mm"
include "sylan.mm"
include "fveq12d.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "eleqtrrd.mm"
include "wkslem1.mm"
include "rspcv.mm"
include "eqeq12.mm"
include "sneq.mm"
include "eqeq12d.mm"
include "preq12.mm"
include "sseq12d.mm"
include "ifpbi123d.mm"
include "sylsyld.mm"
include "com12.mm"
include "3ad2ant3.mm"
include "wlkreslem.mm"
include "eqid.mm"
include "mpbir3and.mm"

theorem wlkres
  let wph: wff ph
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N
  let cV: class V
  let vk: setvar k
  let vi: setvar i
  let vx: setvar x
  assume wlkres.v: |- V = ( Vtx ` G )
  assume wlkres.i: |- I = ( iEdg ` G )
  assume wlkres.d: |- ( ph -> F ( Walks ` G ) P )
  assume wlkres.n: |- ( ph -> N e. ( 0 ..^ ( # ` F ) ) )
  assume wlkres.s: |- ( ph -> ( Vtx ` S ) = V )
  assume wlkres.e: |- ( ph -> ( iEdg ` S ) = ( I |` ( F " ( 0 ..^ N ) ) ) )
  assume wlkres.h: |- H = ( F |` ( 0 ..^ N ) )
  assume wlkres.q: |- Q = ( P |` ( 0 ... N ) )


  assert |- ( ph -> H ( Walks ` S ) Q )

  proof
    wph
    cH
    cQ
    cS
    cwlks
    cfv
    wbr
    #
    cH
    cS
    ciedg
    cfv
    #
    cdm
    #
    cword
    #
    wcel
    #
    cc0
    cH
    chash
    cfv
    #
    cfz
    co
    #
    cS
    cvtx
    cfv
    #
    cQ
    wf
    #
    vx
    cv
    #
    cQ
    cfv
    #
    @9
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    wceq
    #
    @9
    cH
    cfv
    #
    @1
    cfv
    #
    @10
    csn
    #
    wceq
    #
    @10
    @12
    cpr
    #
    @15
    wss
    #
    wif
    #
    vx
    cc0
    @5
    cfzo
    co
    #
    wral
    #
    wph
    cH
    cF
    cc0
    cN
    cfzo
    co
    #
    cres
    #
    @3
    wlkres.h
    wph
    cc0
    @24
    chash
    cfv
    #
    cfzo
    co
    #
    @2
    @24
    wf
    #
    @24
    @3
    wcel
    wph
    @27
    @23
    @2
    @24
    wf
    #
    wph
    @24
    @23
    wfn
    #
    @9
    @24
    cfv
    #
    @2
    wcel
    #
    vx
    @23
    wral
    @28
    wph
    cF
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    wfn
    #
    @23
    @33
    wss
    #
    @29
    wph
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cF
    cI
    cdm
    #
    cword
    wcel
    #
    @34
    wlkres.d
    cP
    cF
    cG
    cI
    wlkres.i
    wlkf
    #
    @37
    cF
    wrdfn
    3syl
    #
    wph
    cN
    @33
    wcel
    #
    @32
    cN
    cuz
    cfv
    #
    wcel
    #
    @35
    wlkres.n
    cN
    cc0
    @32
    elfzouz2
    #
    cN
    cc0
    @32
    fzoss2
    3syl
    #
    @33
    @23
    cF
    fnssres
    syl2anc
    wph
    @31
    vx
    @23
    wph
    @9
    @23
    wcel
    #
    wa
    #
    @31
    @30
    cI
    cF
    @23
    cima
    #
    cres
    #
    cdm
    #
    wcel
    #
    @47
    @30
    @48
    @37
    cin
    @50
    @47
    @48
    @37
    @30
    @47
    @30
    @48
    wcel
    vi
    cv
    #
    cF
    cfv
    #
    @30
    wceq
    #
    vi
    @23
    wrex
    @47
    @54
    @9
    cF
    cfv
    #
    @30
    wceq
    #
    vi
    @9
    @23
    wph
    @46
    simpr
    @52
    @9
    wceq
    #
    @54
    @56
    wb
    @47
    @57
    @53
    @55
    @30
    @52
    @9
    cF
    fveq2
    eqeq1d
    adantl
    @47
    @30
    @55
    @46
    @30
    @55
    wceq
    wph
    @9
    @23
    cF
    fvres
    adantl
    #
    eqcomd
    rspcedvd
    @47
    vi
    @33
    @23
    @30
    cF
    wph
    @34
    @46
    @40
    adantr
    wph
    @35
    @46
    @45
    adantr
    fvelimabd
    mpbird
    @47
    @30
    @55
    @37
    @58
    wph
    @46
    @55
    @37
    wcel
    #
    @38
    wph
    @46
    @59
    wi
    #
    wph
    @36
    @38
    wlkres.d
    @39
    syl
    #
    @38
    @33
    @37
    cF
    wf
    #
    wph
    @60
    wi
    @37
    cF
    wrdf
    #
    @62
    wph
    @46
    @59
    @9
    @33
    wcel
    #
    @62
    @59
    @47
    @62
    @64
    @59
    @33
    @37
    @9
    cF
    ffvelrn
    expcom
    wph
    @23
    @33
    @9
    @45
    sselda
    syl11
    expd
    syl
    mpcom
    imp
    eqeltrd
    elind
    cI
    @48
    dmres
    syl6eleqr
    wph
    @31
    @51
    wb
    @46
    wph
    @2
    @50
    @30
    wph
    @1
    @49
    wlkres.e
    dmeqd
    eleq2d
    adantr
    mpbird
    ralrimiva
    vx
    @23
    @2
    @24
    ffnfv
    sylanbrc
    wph
    @26
    @23
    @2
    @24
    wph
    @25
    cN
    cc0
    cfzo
    wph
    @38
    cN
    cc0
    @32
    cfz
    co
    #
    wcel
    #
    @25
    cN
    wceq
    @61
    wph
    @33
    @65
    cN
    cc0
    @32
    fzossfz
    wlkres.n
    sseldi
    #
    @37
    cF
    cN
    wlkreslem0
    syl2anc
    #
    oveq2d
    feq2d
    mpbird
    @2
    @24
    iswrdb
    sylibr
    syl5eqel
    wph
    @6
    @7
    cP
    cc0
    cN
    cfz
    co
    #
    cres
    #
    wf
    #
    @8
    wph
    @71
    @69
    @7
    @70
    wf
    wph
    @65
    @7
    @69
    cP
    wph
    @65
    @7
    cP
    wf
    @65
    cV
    cP
    wf
    #
    wph
    @36
    @72
    wlkres.d
    cP
    cF
    cG
    cV
    wlkres.v
    wlkp
    syl
    wph
    @7
    cV
    cP
    @65
    wlkres.s
    feq3d
    mpbird
    wph
    @66
    @43
    @69
    @65
    wss
    @67
    cN
    cc0
    @32
    elfzuz3
    cN
    cc0
    @32
    fzss2
    3syl
    fssresd
    wph
    @6
    @69
    @7
    @70
    wph
    @5
    cN
    cc0
    cfz
    wph
    @5
    @25
    cN
    cH
    @24
    chash
    wlkres.h
    fveq2i
    @68
    syl5eq
    #
    oveq2d
    feq2d
    mpbird
    @6
    @7
    cQ
    @70
    wlkres.q
    feq1i
    sylibr
    wph
    @20
    vx
    @21
    @38
    @72
    vk
    cv
    #
    cP
    cfv
    #
    @74
    c1
    caddc
    co
    cP
    cfv
    #
    wceq
    @74
    cF
    cfv
    cI
    cfv
    #
    @75
    csn
    wceq
    @75
    @76
    cpr
    @77
    wss
    wif
    #
    vk
    @33
    wral
    #
    w3a
    #
    wph
    @9
    @21
    wcel
    #
    wa
    #
    @20
    wph
    @80
    @81
    wph
    @36
    @80
    wlkres.d
    cG
    cvv
    wcel
    cF
    cvv
    wcel
    cP
    cvv
    wcel
    w3a
    #
    @36
    @80
    cP
    cF
    cG
    wlkv
    @83
    @36
    @80
    cP
    cvv
    vk
    cF
    cG
    cI
    cV
    cvv
    cvv
    wlkres.v
    wlkres.i
    iswlk
    biimpd
    mpcom
    syl
    adantr
    @79
    @38
    @82
    @20
    wi
    @72
    @82
    @79
    @20
    @82
    @9
    cP
    cfv
    #
    @10
    wceq
    #
    @11
    cP
    cfv
    #
    @12
    wceq
    #
    wa
    #
    @55
    cI
    cfv
    #
    @15
    wceq
    #
    wa
    #
    @79
    @84
    @86
    wceq
    #
    @89
    @84
    csn
    #
    wceq
    #
    @84
    @86
    cpr
    #
    @89
    wss
    #
    wif
    #
    @20
    @82
    @88
    @90
    wph
    @81
    @88
    wph
    @81
    @46
    @88
    wph
    @21
    @23
    @9
    wph
    @5
    cN
    cc0
    cfzo
    @73
    oveq2d
    eleq2d
    #
    wph
    @46
    @88
    @47
    @85
    @87
    @47
    @10
    @9
    @70
    cfv
    @84
    @9
    cQ
    @70
    wlkres.q
    fveq1i
    @47
    @9
    @69
    cP
    wph
    @23
    @69
    @9
    @23
    @69
    wss
    wph
    cc0
    cN
    fzossfz
    a1i
    sselda
    fvresd
    syl5req
    @47
    @12
    @11
    @70
    cfv
    @86
    @11
    cQ
    @70
    wlkres.q
    fveq1i
    @47
    @11
    @69
    cP
    @46
    @11
    @69
    wcel
    wph
    cc0
    cN
    @9
    fzofzp1
    adantl
    fvresd
    syl5req
    jca
    ex
    sylbid
    imp
    @82
    @89
    @30
    @49
    cfv
    #
    @15
    wph
    @81
    @89
    @99
    wceq
    #
    wph
    @81
    @46
    @100
    @98
    wph
    @46
    @100
    @47
    @99
    @89
    wph
    wph
    @38
    wa
    #
    @46
    @99
    @89
    wceq
    wph
    @38
    @61
    ancli
    @101
    @46
    wa
    @23
    cF
    cI
    @9
    @101
    cF
    wfun
    #
    @46
    @38
    @102
    wph
    @38
    @33
    @37
    cF
    @63
    ffund
    adantl
    adantr
    @101
    @23
    cF
    cdm
    #
    wss
    #
    @46
    @38
    wph
    @104
    @38
    @62
    @103
    @33
    wceq
    #
    wph
    @104
    wi
    @63
    @33
    @37
    cF
    fdm
    wph
    @104
    @105
    @35
    @45
    @103
    @33
    @23
    sseq2
    syl5ibr
    3syl
    impcom
    adantr
    @101
    @46
    simpr
    resfvresima
    sylan
    eqcomd
    ex
    sylbid
    imp
    @82
    @14
    @30
    @1
    @49
    wph
    @1
    @49
    wceq
    @81
    wlkres.e
    adantr
    @14
    @30
    wceq
    @82
    @9
    cH
    @24
    wlkres.h
    fveq1i
    a1i
    fveq12d
    eqtr4d
    jca
    @82
    @64
    @79
    @97
    wi
    wph
    @21
    @33
    @9
    wph
    @32
    @5
    cuz
    cfv
    #
    wcel
    @21
    @33
    wss
    wph
    @32
    @42
    @106
    wph
    @41
    @43
    wlkres.n
    @44
    syl
    wph
    @5
    cN
    cuz
    wph
    @5
    @25
    cN
    wph
    cH
    @24
    chash
    cH
    @24
    wceq
    wph
    wlkres.h
    a1i
    fveq2d
    @68
    eqtrd
    fveq2d
    eleqtrrd
    @5
    cc0
    @32
    fzoss2
    syl
    sselda
    @78
    @97
    vk
    @9
    @33
    @74
    @9
    cP
    cF
    cI
    wkslem1
    rspcv
    syl
    @91
    @97
    @20
    @91
    @92
    @94
    @96
    @13
    @17
    @19
    @88
    @92
    @13
    wb
    @90
    @84
    @10
    @86
    @12
    eqeq12
    adantr
    @91
    @89
    @15
    @93
    @16
    @88
    @90
    simpr
    #
    @88
    @93
    @16
    wceq
    #
    @90
    @85
    @108
    @87
    @84
    @10
    sneq
    adantr
    adantr
    eqeq12d
    @91
    @95
    @18
    @89
    @15
    @88
    @95
    @18
    wceq
    @90
    @84
    @86
    @10
    @12
    preq12
    adantr
    @107
    sseq12d
    ifpbi123d
    biimpd
    sylsyld
    com12
    3ad2ant3
    mpcom
    ralrimiva
    wph
    cS
    cvv
    wcel
    cH
    cvv
    wcel
    cQ
    cvv
    wcel
    w3a
    @0
    @4
    @8
    @22
    w3a
    wb
    wph
    cP
    cQ
    cS
    cF
    cG
    cH
    cI
    cN
    cV
    wlkres.v
    wlkres.i
    wlkres.d
    wlkres.n
    wlkres.s
    wlkres.e
    wlkres.h
    wlkres.q
    wlkreslem
    cQ
    cvv
    vx
    cH
    cS
    @1
    @7
    cvv
    cvv
    @7
    eqid
    @1
    eqid
    iswlk
    syl
    mpbir3and
end
