include "c1.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "ceupth.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "ccsh.mm"
include "cc0.mm"
include "cfzo.mm"
include "cres.mm"
include "chash.mm"
include "cfz.mm"
include "cv.mm"
include "cle.mm"
include "caddc.mm"
include "cif.mm"
include "cmpt.mm"
include "adantl.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "oveq1.mm"
include "wcel.mm"
include "cc.mm"
include "cn0.mm"
include "cn.mm"
include "clt.mm"
include "w3a.mm"
include "elfzo0.mm"
include "nncn.mm"
include "3ad2ant2.mm"
include "sylbi.mm"
include "npcan1.mm"
include "3syl.mm"
include "sylan9eq.mm"
include "oveq2d.mm"
include "cdm.mm"
include "cword.mm"
include "ccrcts.mm"
include "cwlks.mm"
include "crctiswlk.mm"
include "wlkf.mm"
include "syl.mm"
include "cshwn.mm"
include "eqtrd.mm"
include "syl5eqr.mm"
include "csn.mm"
include "wo.mm"
include "cun.mm"
include "eqid.mm"
include "crctcshlem1.mm"
include "fz0sn0fz1.mm"
include "eleq2d.mm"
include "elun.mm"
include "syl6bb.mm"
include "elsni.mm"
include "0le0.mm"
include "syl6eqbr.mm"
include "iftrued.mm"
include "fveq2d.mm"
include "ctrls.mm"
include "crctprop.mm"
include "simpr.mm"
include "eqcomd.mm"
include "adantr.mm"
include "addid2d.mm"
include "sylan9eqr.mm"
include "fveq2.mm"
include "3eqtr4d.mm"
include "sylan2.mm"
include "ex.mm"
include "wn.mm"
include "elfznn.mm"
include "nnnle0.mm"
include "iffalsed.mm"
include "nncnd.mm"
include "pncand.mm"
include "jaod.mm"
include "sylbid.mm"
include "imp.mm"
include "mpteq2dva.mm"
include "subidd.mm"
include "syl5eq.mm"
include "breq2d.mm"
include "fveq2i.mm"
include "oveq1i.mm"
include "oveq1d.mm"
include "ifbieq12d.mm"
include "mpteq2dv.mm"
include "wfn.mm"
include "wf.mm"
include "wlkp.mm"
include "ffn.mm"
include "dffn5.mm"
include "sylib.mm"
include "3brtr4d.mm"
include "elfzolt3.mm"
include "cz.mm"
include "elfzoelz.mm"
include "peano2zd.mm"
include "syl5eqel.mm"
include "cshwlen.mm"
include "syl2anc.mm"
include "breqtrd.mm"
include "ciedg.mm"
include "cdif.mm"
include "cima.mm"
include "3jca.mm"
include "cshimadifsn0.mm"
include "imaeq1i.mm"
include "syl6eq.mm"
include "reseq2d.mm"
include "eucrct2eupth1.mm"
include "a1i.mm"
include "fzossfz.mm"
include "syl5sseq.mm"
include "resmptd.mm"
include "elfzoel2.mm"
include "fzoval.mm"
include "eqtr3d.mm"
include "wi.mm"
include "peano2nn0.mm"
include "3ad2ant1.mm"
include "simpl2.mm"
include "wne.mm"
include "1cnd.mm"
include "nn0cn.mm"
include "subadd2d.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "necon3bbid.mm"
include "cr.mm"
include "nn0red.mm"
include "nnre.mm"
include "wb.mm"
include "nn0z.mm"
include "nnz.mm"
include "zltp1le.mm"
include "syl2an.mm"
include "biimp3a.mm"
include "leltned.mm"
include "biimprd.mm"
include "syl6ibr.mm"
include "impcom.mm"
include "3eltr4d.mm"
include "eucrctshift.mm"
include "simprl.mm"
include "simprr.mm"
include "ad2antlr.mm"
include "ifbieq2d.mm"
include "reseq12d.mm"
include "syl6reqr.mm"
include "mpdan.mm"
include "pm2.61ian.mm"

theorem eucrct2eupth
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cN: class N
  let cV: class V
  assume eucrct2eupth1.v: |- V = ( Vtx ` G )
  assume eucrct2eupth1.i: |- I = ( iEdg ` G )
  assume eucrct2eupth1.d: |- ( ph -> F ( EulerPaths ` G ) P )
  assume eucrct2eupth1.c: |- ( ph -> F ( Circuits ` G ) P )
  assume eucrct2eupth1.s: |- ( Vtx ` S ) = V
  assume eucrct2eupth.n: |- ( ph -> N = ( # ` F ) )
  assume eucrct2eupth.j: |- ( ph -> J e. ( 0 ..^ N ) )
  assume eucrct2eupth.e: |- ( ph -> ( iEdg ` S ) = ( I |` ( F " ( ( 0 ..^ N ) \ { J } ) ) ) )
  assume eucrct2eupth.k: |- K = ( J + 1 )
  assume eucrct2eupth.h: |- H = ( ( F cyclShift K ) |` ( 0 ..^ ( N - 1 ) ) )
  assume eucrct2eupth.q: |- Q = ( x e. ( 0 ..^ N ) |-> if ( x <_ ( N - K ) , ( P ` ( x + K ) ) , ( P ` ( ( x + K ) - N ) ) ) )

  disjoint F x
  disjoint I x
  disjoint J x
  disjoint K x
  disjoint N x
  disjoint P x
  disjoint V x
  disjoint ph x
  assert |- ( ph -> H ( EulerPaths ` S ) Q )

  proof
    cJ
    cN
    c1
    cmin
    co
    #
    wceq
    #
    wph
    cH
    cQ
    cS
    ceupth
    cfv
    #
    wbr
    #
    @1
    wph
    wa
    #
    cF
    cK
    ccsh
    co
    #
    cc0
    @0
    cfzo
    co
    #
    cres
    #
    vx
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    #
    vx
    cv
    #
    cN
    cK
    cmin
    co
    #
    cle
    wbr
    #
    @10
    cK
    caddc
    co
    #
    cP
    cfv
    #
    @13
    cN
    cmin
    co
    #
    cP
    cfv
    #
    cif
    #
    cmpt
    #
    cc0
    @0
    cfz
    co
    #
    cres
    #
    cH
    cQ
    @2
    @4
    @18
    @20
    cS
    @5
    cG
    @7
    cI
    @0
    cV
    eucrct2eupth1.v
    eucrct2eupth1.i
    @4
    cF
    cP
    @5
    @18
    cG
    ceupth
    cfv
    #
    wph
    cF
    cP
    @21
    wbr
    #
    @1
    eucrct2eupth1.d
    adantl
    @4
    @5
    cF
    cJ
    c1
    caddc
    co
    #
    ccsh
    co
    #
    cF
    @23
    cK
    cF
    ccsh
    cK
    @23
    eucrct2eupth.k
    eqcomi
    oveq2i
    #
    @4
    @24
    cF
    cN
    ccsh
    co
    #
    cF
    @4
    @23
    cN
    cF
    ccsh
    @1
    wph
    @23
    @0
    c1
    caddc
    co
    #
    cN
    cJ
    @0
    c1
    caddc
    oveq1
    #
    wph
    cJ
    cc0
    cN
    cfzo
    co
    #
    wcel
    #
    cN
    cc
    wcel
    #
    @27
    cN
    wceq
    eucrct2eupth.j
    @30
    cJ
    cn0
    wcel
    #
    cN
    cn
    wcel
    #
    cJ
    cN
    clt
    wbr
    #
    w3a
    #
    @31
    cJ
    cN
    elfzo0
    #
    @33
    @32
    @31
    @34
    cN
    nncn
    3ad2ant2
    #
    sylbi
    #
    cN
    npcan1
    3syl
    #
    sylan9eq
    oveq2d
    wph
    @26
    cF
    wceq
    @1
    wph
    @26
    cF
    @8
    ccsh
    co
    #
    cF
    wph
    cN
    @8
    cF
    ccsh
    eucrct2eupth.n
    oveq2d
    wph
    cF
    cI
    cdm
    #
    cword
    wcel
    #
    @40
    cF
    wceq
    wph
    cF
    cP
    cG
    ccrcts
    cfv
    #
    wbr
    #
    @42
    eucrct2eupth1.c
    @44
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    @42
    cP
    cF
    cG
    crctiswlk
    #
    cP
    cF
    cG
    cI
    eucrct2eupth1.i
    wlkf
    syl
    syl
    #
    @41
    cF
    cshwn
    syl
    eqtrd
    adantl
    eqtrd
    syl5eqr
    #
    @4
    vx
    @9
    @10
    cc0
    cle
    wbr
    #
    @10
    cN
    caddc
    co
    #
    cP
    cfv
    #
    @50
    cN
    cmin
    co
    #
    cP
    cfv
    #
    cif
    #
    cmpt
    #
    vx
    @9
    @10
    cP
    cfv
    #
    cmpt
    #
    @18
    cP
    wph
    @55
    @57
    wceq
    @1
    wph
    vx
    @9
    @54
    @56
    wph
    @10
    @9
    wcel
    #
    @54
    @56
    wceq
    #
    wph
    @58
    @10
    cc0
    csn
    #
    wcel
    #
    @10
    c1
    @8
    cfz
    co
    #
    wcel
    #
    wo
    #
    @59
    wph
    @58
    @10
    @60
    @62
    cun
    #
    wcel
    @64
    wph
    @9
    @65
    @10
    wph
    @8
    cn0
    wcel
    @9
    @65
    wceq
    wph
    cP
    cF
    cG
    cI
    @8
    cV
    eucrct2eupth1.v
    eucrct2eupth1.i
    eucrct2eupth1.c
    @8
    eqid
    #
    crctcshlem1
    @8
    fz0sn0fz1
    syl
    eleq2d
    @10
    @60
    @62
    elun
    syl6bb
    wph
    @61
    @59
    @63
    wph
    @61
    @59
    wph
    @61
    wa
    #
    @54
    @51
    @56
    @67
    @49
    @51
    @53
    @61
    @49
    wph
    @61
    @10
    cc0
    cc0
    cle
    @10
    cc0
    elsni
    #
    0le0
    syl6eqbr
    adantl
    iftrued
    @61
    wph
    @10
    cc0
    wceq
    #
    @51
    @56
    wceq
    @68
    wph
    @69
    wa
    #
    cN
    cP
    cfv
    #
    cc0
    cP
    cfv
    #
    @51
    @56
    wph
    @71
    @72
    wceq
    @69
    wph
    @71
    @8
    cP
    cfv
    #
    @72
    wph
    cN
    @8
    cP
    eucrct2eupth.n
    fveq2d
    wph
    @44
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    #
    @72
    @73
    wceq
    #
    wa
    #
    @73
    @72
    wceq
    eucrct2eupth1.c
    cP
    cF
    cG
    crctprop
    @76
    @72
    @73
    @74
    @75
    simpr
    eqcomd
    3syl
    eqtrd
    adantr
    @70
    @50
    cN
    cP
    @69
    wph
    @50
    cc0
    cN
    caddc
    co
    cN
    @10
    cc0
    cN
    caddc
    oveq1
    wph
    cN
    wph
    @30
    @31
    eucrct2eupth.j
    @38
    syl
    #
    addid2d
    sylan9eqr
    fveq2d
    @69
    @56
    @72
    wceq
    wph
    @10
    cc0
    cP
    fveq2
    adantl
    3eqtr4d
    sylan2
    eqtrd
    ex
    wph
    @63
    @59
    wph
    @63
    wa
    #
    @54
    @53
    @56
    @78
    @49
    @51
    @53
    @63
    @49
    wn
    #
    wph
    @63
    @10
    cn
    wcel
    @79
    @10
    @8
    elfznn
    #
    @10
    nnnle0
    syl
    adantl
    iffalsed
    @78
    @52
    @10
    cP
    @78
    @10
    cN
    @63
    @10
    cc
    wcel
    wph
    @63
    @10
    @80
    nncnd
    adantl
    wph
    @31
    @63
    @77
    adantr
    pncand
    fveq2d
    eqtrd
    ex
    jaod
    sylbid
    imp
    mpteq2dva
    adantl
    @4
    vx
    @9
    @17
    @54
    @4
    @12
    @49
    @14
    @16
    @51
    @53
    @4
    @11
    cc0
    @10
    cle
    @4
    @11
    cN
    @23
    cmin
    co
    #
    cc0
    cK
    @23
    cN
    cmin
    eucrct2eupth.k
    oveq2i
    @1
    wph
    @81
    cN
    @27
    cmin
    co
    #
    cc0
    @1
    @23
    @27
    cN
    cmin
    @28
    oveq2d
    wph
    @82
    cN
    cN
    cmin
    co
    cc0
    wph
    @27
    cN
    cN
    cmin
    @39
    oveq2d
    wph
    cN
    @77
    subidd
    eqtrd
    sylan9eq
    syl5eq
    breq2d
    @4
    @14
    @10
    @23
    caddc
    co
    #
    cP
    cfv
    @51
    @13
    @83
    cP
    cK
    @23
    @10
    caddc
    eucrct2eupth.k
    oveq2i
    #
    fveq2i
    @4
    @83
    @50
    cP
    @1
    wph
    @83
    @10
    @27
    caddc
    co
    #
    @50
    @1
    @23
    @27
    @10
    caddc
    @28
    oveq2d
    #
    wph
    @27
    cN
    @10
    caddc
    @39
    oveq2d
    #
    sylan9eq
    fveq2d
    syl5eq
    @4
    @16
    @83
    cN
    cmin
    co
    #
    cP
    cfv
    @53
    @15
    @88
    cP
    @13
    @83
    cN
    cmin
    @84
    oveq1i
    fveq2i
    @4
    @88
    @52
    cP
    @1
    wph
    @88
    @85
    cN
    cmin
    co
    @52
    @1
    @83
    @85
    cN
    cmin
    @86
    oveq1d
    wph
    @85
    @50
    cN
    cmin
    @87
    oveq1d
    sylan9eq
    fveq2d
    syl5eq
    ifbieq12d
    mpteq2dv
    @4
    cP
    @9
    wfn
    #
    cP
    @57
    wceq
    wph
    @89
    @1
    wph
    @45
    @9
    cV
    cP
    wf
    @89
    wph
    @44
    @45
    eucrct2eupth1.c
    @46
    syl
    cP
    cF
    cG
    cV
    eucrct2eupth1.v
    wlkp
    @9
    cV
    cP
    ffn
    3syl
    adantl
    vx
    @9
    cP
    dffn5
    sylib
    3eqtr4d
    #
    3brtr4d
    @4
    cF
    cP
    @5
    @18
    @43
    wph
    @44
    @1
    eucrct2eupth1.c
    adantl
    @48
    @90
    3brtr4d
    eucrct2eupth1.s
    wph
    cc0
    @5
    chash
    cfv
    #
    clt
    wbr
    #
    @1
    wph
    cc0
    cN
    @91
    clt
    wph
    @30
    cc0
    cN
    clt
    wbr
    eucrct2eupth.j
    cJ
    cc0
    cN
    elfzolt3
    syl
    wph
    cN
    @8
    @91
    eucrct2eupth.n
    wph
    @42
    cK
    cz
    wcel
    #
    @8
    @91
    wceq
    @47
    wph
    cK
    @23
    cz
    eucrct2eupth.k
    wph
    cJ
    wph
    @30
    cJ
    cz
    wcel
    #
    eucrct2eupth.j
    cJ
    cc0
    cN
    elfzoelz
    syl
    peano2zd
    syl5eqel
    @42
    @93
    wa
    @91
    @8
    cK
    @41
    cF
    cshwlen
    eqcomd
    syl2anc
    eqtrd
    #
    breqtrd
    #
    adantl
    @4
    cN
    @91
    c1
    cmin
    wph
    cN
    @91
    wceq
    @1
    @95
    adantl
    oveq1d
    @4
    cS
    ciedg
    cfv
    #
    cI
    cF
    @29
    cJ
    csn
    cdif
    cima
    #
    cres
    #
    cI
    @5
    @6
    cima
    #
    cres
    #
    wph
    @97
    @99
    wceq
    #
    @1
    eucrct2eupth.e
    adantl
    @4
    @98
    @100
    cI
    @4
    @98
    @24
    @6
    cima
    #
    @100
    @4
    @42
    cN
    @8
    wceq
    #
    @30
    w3a
    #
    @98
    @103
    wceq
    #
    wph
    @105
    @1
    wph
    @42
    @104
    @30
    @47
    eucrct2eupth.n
    eucrct2eupth.j
    3jca
    #
    adantl
    @41
    cF
    cJ
    cN
    cshimadifsn0
    #
    syl
    @24
    @5
    @6
    @25
    imaeq1i
    #
    syl6eq
    reseq2d
    eqtrd
    @7
    eqid
    #
    @20
    eqid
    eucrct2eupth1
    cH
    @7
    wceq
    #
    @4
    eucrct2eupth.h
    a1i
    wph
    cQ
    @20
    wceq
    @1
    wph
    cQ
    vx
    @29
    @17
    cmpt
    #
    @20
    eucrct2eupth.q
    wph
    @18
    @29
    cres
    #
    @112
    @20
    wph
    vx
    @9
    @29
    @17
    wph
    cc0
    cN
    cfz
    co
    #
    @29
    @9
    cc0
    cN
    fzossfz
    #
    wph
    cN
    @8
    cc0
    cfz
    eucrct2eupth.n
    oveq2d
    syl5sseq
    resmptd
    wph
    @29
    @19
    @18
    wph
    @30
    cN
    cz
    wcel
    #
    @29
    @19
    wceq
    eucrct2eupth.j
    cJ
    cc0
    cN
    elfzoel2
    cc0
    cN
    fzoval
    3syl
    #
    reseq2d
    eqtr3d
    syl5eq
    adantl
    3brtr4d
    @1
    wn
    #
    wph
    wa
    #
    @5
    vx
    @9
    @10
    @8
    cK
    cmin
    co
    #
    cle
    wbr
    #
    @14
    @13
    @8
    cmin
    co
    #
    cP
    cfv
    #
    cif
    #
    cmpt
    #
    @21
    wbr
    #
    @5
    @125
    @43
    wbr
    #
    wa
    #
    @3
    @119
    vx
    cP
    @125
    cK
    cF
    cG
    @5
    cI
    @8
    cV
    eucrct2eupth1.v
    eucrct2eupth1.i
    wph
    @44
    @118
    eucrct2eupth1.c
    adantl
    @66
    @119
    @23
    @29
    cK
    cc0
    @8
    cfzo
    co
    #
    wph
    @118
    @23
    @29
    wcel
    #
    wph
    @30
    @118
    @130
    wi
    eucrct2eupth.j
    @30
    @118
    @23
    cn0
    wcel
    #
    @33
    @23
    cN
    clt
    wbr
    #
    w3a
    #
    @130
    @30
    @35
    @118
    @133
    wi
    @36
    @35
    @118
    @133
    @35
    @118
    wa
    @131
    @33
    @132
    @35
    @131
    @118
    @32
    @33
    @131
    @34
    cJ
    peano2nn0
    #
    3ad2ant1
    adantr
    @32
    @33
    @34
    @118
    simpl2
    @35
    @118
    @132
    @35
    @118
    cN
    @23
    wne
    #
    @132
    @35
    @1
    cN
    @23
    @35
    @0
    cJ
    wceq
    @23
    cN
    wceq
    @1
    cN
    @23
    wceq
    @35
    cN
    c1
    cJ
    @37
    @35
    1cnd
    @32
    @33
    cJ
    cc
    wcel
    @34
    cJ
    nn0cn
    3ad2ant1
    subadd2d
    cJ
    @0
    eqcom
    cN
    @23
    eqcom
    3bitr4g
    necon3bbid
    @35
    @132
    @135
    @35
    @23
    cN
    @32
    @33
    @23
    cr
    wcel
    @34
    @32
    @23
    @134
    nn0red
    3ad2ant1
    @33
    @32
    cN
    cr
    wcel
    @34
    cN
    nnre
    3ad2ant2
    @32
    @33
    @34
    @23
    cN
    cle
    wbr
    #
    @32
    @94
    @116
    @34
    @136
    wb
    @33
    cJ
    nn0z
    cN
    nnz
    cJ
    cN
    zltp1le
    syl2an
    biimp3a
    leltned
    biimprd
    sylbid
    imp
    3jca
    ex
    sylbi
    @23
    cN
    elfzo0
    syl6ibr
    syl
    impcom
    cK
    @23
    wceq
    @119
    eucrct2eupth.k
    a1i
    wph
    @129
    @29
    wceq
    @118
    wph
    @8
    cN
    cc0
    cfzo
    wph
    cN
    @8
    eucrct2eupth.n
    eqcomd
    #
    oveq2d
    adantl
    3eltr4d
    @5
    eqid
    @125
    eqid
    wph
    @22
    @118
    eucrct2eupth1.d
    adantl
    eucrctshift
    @119
    @128
    wa
    #
    @7
    @125
    @19
    cres
    #
    cH
    cQ
    @2
    @138
    @125
    @139
    cS
    @5
    cG
    @7
    cI
    @0
    cV
    eucrct2eupth1.v
    eucrct2eupth1.i
    @119
    @126
    @127
    simprl
    @119
    @126
    @127
    simprr
    eucrct2eupth1.s
    wph
    @92
    @118
    @128
    @96
    ad2antlr
    wph
    @0
    @91
    c1
    cmin
    co
    wceq
    @118
    @128
    wph
    cN
    @91
    c1
    cmin
    @95
    oveq1d
    ad2antlr
    @119
    @97
    @101
    wceq
    @128
    @119
    @97
    @99
    @101
    wph
    @102
    @118
    eucrct2eupth.e
    adantl
    @119
    @98
    @100
    cI
    @119
    @98
    @103
    @100
    @119
    @105
    @106
    wph
    @105
    @118
    @107
    adantl
    @108
    syl
    @109
    syl6eq
    reseq2d
    eqtrd
    adantr
    @110
    @139
    eqid
    eucrct2eupth1
    @111
    @138
    eucrct2eupth.h
    a1i
    @119
    cQ
    @139
    wceq
    @128
    @119
    @139
    @112
    cQ
    @119
    @139
    @113
    @112
    @119
    @125
    @18
    @19
    @29
    @119
    vx
    @9
    @124
    @17
    @119
    @121
    @12
    @123
    @16
    @14
    wph
    @121
    @12
    wb
    @118
    wph
    @120
    @11
    @10
    cle
    wph
    @8
    cN
    cK
    cmin
    @137
    oveq1d
    breq2d
    adantl
    wph
    @123
    @16
    wceq
    @118
    wph
    @122
    @15
    cP
    wph
    @8
    cN
    @13
    cmin
    @137
    oveq2d
    fveq2d
    adantl
    ifbieq2d
    mpteq2dv
    wph
    @19
    @29
    wceq
    @118
    wph
    @29
    @19
    @117
    eqcomd
    adantl
    reseq12d
    @119
    vx
    @9
    @29
    @17
    @119
    @114
    @29
    @9
    @115
    @119
    cN
    @8
    cc0
    cfz
    wph
    @104
    @118
    eucrct2eupth.n
    adantl
    oveq2d
    syl5sseq
    resmptd
    eqtrd
    eucrct2eupth.q
    syl6reqr
    adantr
    3brtr4d
    mpdan
    pm2.61ian
end
