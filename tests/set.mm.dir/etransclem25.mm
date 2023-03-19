include "cfa.mm"
include "cfv.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cprod.mm"
include "cdiv.mm"
include "c1.mm"
include "cmin.mm"
include "clt.mm"
include "wbr.mm"
include "cexp.mm"
include "cmul.mm"
include "cif.mm"
include "cdvds.mm"
include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "nnnn0d.mm"
include "faccld.mm"
include "nnzd.mm"
include "csu.mm"
include "cn.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "nfcv.mm"
include "fzfid.mm"
include "wf.mm"
include "cn0.mm"
include "cmap.mm"
include "cvv.mm"
include "wss.mm"
include "nn0ex.mm"
include "fzssnn0.mm"
include "mapss.mm"
include "mp2an.mm"
include "wb.mm"
include "ovex.mm"
include "ovexd.mm"
include "elmapg.mm"
include "sylancr.mm"
include "ibir.mm"
include "sseldi.mm"
include "syl.mm"
include "mccl.mm"
include "eqeltrd.mm"
include "elfzelzd.mm"
include "etransclem10.mm"
include "zmulcld.mm"
include "wa.mm"
include "adantr.mm"
include "caddc.mm"
include "0z.mm"
include "fzp1ss.mm"
include "ax-mp.mm"
include "id.mm"
include "1e0p1.mm"
include "oveq1i.mm"
include "syl6eleq.mm"
include "adantl.mm"
include "etransclem3.mm"
include "fprodzcl.mm"
include "3jca.mm"
include "csn.mm"
include "cdif.mm"
include "zcnd.mm"
include "subidd.mm"
include "oveq2d.mm"
include "ifeq2d.mm"
include "cfn.mm"
include "fzfi.mm"
include "diffi.mm"
include "mp1i.mm"
include "eldifi.mm"
include "dvds0.mm"
include "wceq.mm"
include "iftrue.mm"
include "breqtrd.mm"
include "wn.mm"
include "iddvds.mm"
include "ad2antrr.mm"
include "iffalse.mm"
include "ad2antlr.mm"
include "oveq1.mm"
include "cc.mm"
include "ffvelrnd.mm"
include "eqtrd.mm"
include "fac0.mm"
include "syl6eq.mm"
include "nncnd.mm"
include "div1d.mm"
include "0cnd.mm"
include "exp0d.mm"
include "oveq12d.mm"
include "mulid1d.mm"
include "adantlr.mm"
include "eqtr2d.mm"
include "simpr.mm"
include "iffalsed.mm"
include "simpll.mm"
include "cr.mm"
include "zred.mm"
include "nnred.mm"
include "cle.mm"
include "nltled.mm"
include "wne.mm"
include "neqne.mm"
include "leneltd.mm"
include "zsubcld.mm"
include "posdifd.mm"
include "mpbid.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "0expd.mm"
include "nnne0d.mm"
include "divcld.mm"
include "mul01d.mm"
include "syl2anc.mm"
include "pm2.61dan.mm"
include "dvdsmultr1d.mm"
include "fveq2.mm"
include "breq2d.mm"
include "oveq2.mm"
include "sylan9eqr.mm"
include "ifbieq2d.mm"
include "fprodsplit1.mm"
include "breqtrrd.mm"
include "dvdsmultr2.mm"
include "sylc.mm"
include "ffvelrnda.mm"
include "fprodcl.mm"
include "fprodn0.mm"
include "mulassd.mm"
include "syl6eqr.mm"

theorem etransclem25
  let wph: wff ph
  let cC: class C
  let cP: class P
  let cT: class T
  let vj: setvar j
  let cJ: class J
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  assume etransclem25.p: |- ( ph -> P e. NN )
  assume etransclem25.m: |- ( ph -> M e. NN0 )
  assume etransclem25.n: |- ( ph -> N e. NN0 )
  assume etransclem25.c: |- ( ph -> C : ( 0 ... M ) --> ( 0 ... N ) )
  assume etransclem25.sumc: |- ( ph -> sum_ j e. ( 0 ... M ) ( C ` j ) = N )
  assume etransclem25.t: |- T = ( ( ( ! ` N ) / prod_ j e. ( 0 ... M ) ( ! ` ( C ` j ) ) ) x. ( if ( ( P - 1 ) < ( C ` 0 ) , 0 , ( ( ( ! ` ( P - 1 ) ) / ( ! ` ( ( P - 1 ) - ( C ` 0 ) ) ) ) x. ( J ^ ( ( P - 1 ) - ( C ` 0 ) ) ) ) ) x. prod_ j e. ( 1 ... M ) if ( P < ( C ` j ) , 0 , ( ( ( ! ` P ) / ( ! ` ( P - ( C ` j ) ) ) ) x. ( ( J - j ) ^ ( P - ( C ` j ) ) ) ) ) ) )
  assume etransclem25.j: |- ( ph -> J e. ( 1 ... M ) )

  disjoint C j
  disjoint J j
  disjoint M j
  disjoint P j
  disjoint j ph
  disjoint k x
  assert |- ( ph -> ( ! ` P ) || T )

  proof
    wph
    cP
    cfa
    cfv
    #
    cN
    cfa
    cfv
    #
    cc0
    cM
    cfz
    co
    #
    vj
    cv
    #
    cC
    cfv
    #
    cfa
    cfv
    #
    vj
    cprod
    #
    cdiv
    co
    #
    cP
    c1
    cmin
    co
    #
    cc0
    cC
    cfv
    #
    clt
    wbr
    cc0
    @8
    cfa
    cfv
    @8
    @9
    cmin
    co
    #
    cfa
    cfv
    cdiv
    co
    cJ
    @10
    cexp
    co
    cmul
    co
    cif
    #
    cmul
    co
    #
    c1
    cM
    cfz
    co
    #
    cP
    @4
    clt
    wbr
    #
    cc0
    @0
    cP
    @4
    cmin
    co
    #
    cfa
    cfv
    #
    cdiv
    co
    #
    cJ
    @3
    cmin
    co
    #
    @15
    cexp
    co
    #
    cmul
    co
    #
    cif
    #
    vj
    cprod
    #
    cmul
    co
    #
    cT
    cdvds
    wph
    @0
    cz
    wcel
    #
    @12
    cz
    wcel
    #
    @22
    cz
    wcel
    #
    w3a
    @0
    @22
    cdvds
    wbr
    @0
    @23
    cdvds
    wbr
    wph
    @24
    @25
    @26
    wph
    @0
    wph
    cP
    wph
    cP
    etransclem25.p
    nnnn0d
    faccld
    #
    nnzd
    #
    wph
    @7
    @11
    wph
    @7
    wph
    @7
    @2
    @4
    vj
    csu
    #
    cfa
    cfv
    #
    @6
    cdiv
    co
    cn
    wph
    @1
    @30
    @6
    cdiv
    wph
    cN
    @29
    cfa
    wph
    @29
    cN
    etransclem25.sumc
    eqcomd
    fveq2d
    oveq1d
    wph
    @2
    cC
    vj
    vj
    cC
    nfcv
    wph
    cc0
    cM
    fzfid
    #
    wph
    @2
    cc0
    cN
    cfz
    co
    #
    cC
    wf
    #
    cC
    cn0
    @2
    cmap
    co
    #
    wcel
    etransclem25.c
    @33
    @32
    @2
    cmap
    co
    #
    @34
    cC
    cn0
    cvv
    wcel
    @32
    cn0
    wss
    @35
    @34
    wss
    nn0ex
    cN
    fzssnn0
    #
    @32
    cn0
    @2
    cvv
    mapss
    mp2an
    @33
    cC
    @35
    wcel
    #
    @33
    @32
    cvv
    wcel
    @2
    cvv
    wcel
    @37
    @33
    wb
    cc0
    cN
    cfz
    ovex
    @33
    cc0
    cM
    cfz
    ovexd
    @32
    @2
    cC
    cvv
    cvv
    elmapg
    sylancr
    ibir
    sseldi
    syl
    mccl
    eqeltrd
    nnzd
    wph
    cC
    cP
    cJ
    cM
    cN
    etransclem25.p
    etransclem25.m
    etransclem25.c
    wph
    cJ
    c1
    cM
    etransclem25.j
    elfzelzd
    #
    etransclem10
    #
    zmulcld
    wph
    @13
    @21
    vj
    wph
    c1
    cM
    fzfid
    #
    wph
    @3
    @13
    wcel
    #
    wa
    #
    cC
    cP
    @3
    cJ
    cM
    cN
    wph
    cP
    cn
    wcel
    #
    @41
    etransclem25.p
    adantr
    wph
    @33
    @41
    etransclem25.c
    adantr
    @41
    @3
    @2
    wcel
    #
    wph
    @41
    cc0
    c1
    caddc
    co
    #
    cM
    cfz
    co
    #
    @2
    @3
    cc0
    cz
    wcel
    @46
    @2
    wss
    0z
    cc0
    cM
    fzp1ss
    ax-mp
    #
    @41
    @3
    @13
    @46
    @41
    id
    c1
    @45
    cM
    cfz
    1e0p1
    oveq1i
    #
    syl6eleq
    sseldi
    #
    adantl
    wph
    cJ
    cz
    wcel
    #
    @41
    @38
    adantr
    etransclem3
    #
    fprodzcl
    3jca
    wph
    @0
    cP
    cJ
    cC
    cfv
    #
    clt
    wbr
    #
    cc0
    @0
    cP
    @52
    cmin
    co
    #
    cfa
    cfv
    #
    cdiv
    co
    #
    cc0
    @54
    cexp
    co
    #
    cmul
    co
    #
    cif
    #
    @13
    cJ
    csn
    #
    cdif
    #
    @21
    vj
    cprod
    #
    cmul
    co
    @22
    cdvds
    wph
    @0
    @59
    @62
    @28
    wph
    @59
    @53
    cc0
    @56
    cJ
    cJ
    cmin
    co
    #
    @54
    cexp
    co
    #
    cmul
    co
    #
    cif
    cz
    wph
    @53
    @58
    @65
    cc0
    wph
    @57
    @64
    @56
    cmul
    wph
    cc0
    @63
    @54
    cexp
    wph
    @63
    cc0
    wph
    cJ
    wph
    cJ
    @38
    zcnd
    subidd
    #
    eqcomd
    oveq1d
    oveq2d
    ifeq2d
    wph
    cC
    cP
    cJ
    cJ
    cM
    cN
    etransclem25.p
    etransclem25.c
    wph
    cJ
    @13
    wcel
    #
    cJ
    @2
    wcel
    etransclem25.j
    @67
    @46
    @2
    cJ
    @47
    @67
    cJ
    @13
    @46
    @67
    id
    @48
    syl6eleq
    sseldi
    syl
    #
    @38
    etransclem3
    eqeltrd
    wph
    @61
    @21
    vj
    @13
    cfn
    wcel
    @61
    cfn
    wcel
    wph
    c1
    cM
    fzfi
    @13
    @60
    diffi
    mp1i
    wph
    @3
    @61
    wcel
    #
    wa
    cC
    cP
    @3
    cJ
    cM
    cN
    wph
    @43
    @69
    etransclem25.p
    adantr
    wph
    @33
    @69
    etransclem25.c
    adantr
    @69
    @44
    wph
    @69
    @41
    @44
    @3
    @13
    @60
    eldifi
    @49
    syl
    adantl
    wph
    @50
    @69
    @38
    adantr
    etransclem3
    fprodzcl
    wph
    @53
    @0
    @59
    cdvds
    wbr
    #
    wph
    @53
    wa
    @0
    cc0
    @59
    cdvds
    wph
    @0
    cc0
    cdvds
    wbr
    #
    @53
    wph
    @24
    @71
    @28
    @0
    dvds0
    syl
    #
    adantr
    @53
    cc0
    @59
    wceq
    wph
    @53
    @59
    cc0
    @53
    cc0
    @58
    iftrue
    eqcomd
    adantl
    breqtrd
    wph
    @53
    wn
    #
    wa
    #
    cP
    @52
    wceq
    #
    @70
    @74
    @75
    wa
    #
    @0
    @0
    @59
    cdvds
    wph
    @0
    @0
    cdvds
    wbr
    #
    @73
    @75
    wph
    @24
    @77
    @28
    @0
    iddvds
    syl
    ad2antrr
    @76
    @59
    @58
    @0
    @73
    @59
    @58
    wceq
    wph
    @75
    @53
    cc0
    @58
    iffalse
    ad2antlr
    wph
    @75
    @58
    @0
    wceq
    @73
    wph
    @75
    wa
    #
    @58
    @0
    c1
    cmul
    co
    #
    @0
    @78
    @56
    @0
    @57
    c1
    cmul
    @78
    @56
    @0
    c1
    cdiv
    co
    #
    @0
    @78
    @55
    c1
    @0
    cdiv
    @78
    @55
    cc0
    cfa
    cfv
    c1
    @78
    @54
    cc0
    cfa
    @78
    @54
    @52
    @52
    cmin
    co
    #
    cc0
    @75
    @54
    @81
    wceq
    wph
    cP
    @52
    @52
    cmin
    oveq1
    adantl
    @78
    @52
    wph
    @52
    cc
    wcel
    @75
    wph
    @52
    wph
    @52
    cc0
    cN
    wph
    @2
    @32
    cJ
    cC
    etransclem25.c
    @68
    ffvelrnd
    elfzelzd
    #
    zcnd
    adantr
    subidd
    eqtrd
    #
    fveq2d
    fac0
    syl6eq
    oveq2d
    wph
    @80
    @0
    wceq
    @75
    wph
    @0
    wph
    @0
    @27
    nncnd
    #
    div1d
    adantr
    eqtrd
    @78
    @57
    cc0
    cc0
    cexp
    co
    c1
    @78
    @54
    cc0
    cc0
    cexp
    @83
    oveq2d
    @78
    cc0
    @78
    0cnd
    exp0d
    eqtrd
    oveq12d
    wph
    @79
    @0
    wceq
    @75
    wph
    @0
    @84
    mulid1d
    adantr
    eqtrd
    adantlr
    eqtr2d
    breqtrd
    @74
    @75
    wn
    #
    wa
    #
    @0
    cc0
    @59
    cdvds
    wph
    @71
    @73
    @85
    @72
    ad2antrr
    @86
    @59
    @58
    cc0
    @86
    @53
    cc0
    @58
    @74
    @73
    @85
    wph
    @73
    simpr
    #
    adantr
    iffalsed
    @86
    wph
    @52
    cP
    clt
    wbr
    #
    @58
    cc0
    wceq
    wph
    @73
    @85
    simpll
    @86
    @52
    cP
    wph
    @52
    cr
    wcel
    #
    @73
    @85
    wph
    @52
    @82
    zred
    #
    ad2antrr
    wph
    cP
    cr
    wcel
    #
    @73
    @85
    wph
    cP
    etransclem25.p
    nnred
    #
    ad2antrr
    @74
    @52
    cP
    cle
    wbr
    @85
    @74
    @52
    cP
    wph
    @89
    @73
    @90
    adantr
    wph
    @91
    @73
    @92
    adantr
    @87
    nltled
    adantr
    @85
    cP
    @52
    wne
    @74
    cP
    @52
    neqne
    adantl
    leneltd
    wph
    @88
    wa
    #
    @58
    @56
    cc0
    cmul
    co
    cc0
    @93
    @57
    cc0
    @56
    cmul
    @93
    @54
    @93
    @54
    cz
    wcel
    cc0
    @54
    clt
    wbr
    #
    @54
    cn
    wcel
    @93
    cP
    @52
    wph
    cP
    cz
    wcel
    @88
    wph
    cP
    etransclem25.p
    nnzd
    adantr
    wph
    @52
    cz
    wcel
    @88
    @82
    adantr
    zsubcld
    @93
    @88
    @94
    wph
    @88
    simpr
    @93
    @52
    cP
    wph
    @89
    @88
    @90
    adantr
    wph
    @91
    @88
    @92
    adantr
    posdifd
    mpbid
    @54
    elnnz
    sylanbrc
    #
    0expd
    oveq2d
    @93
    @56
    @93
    @0
    @55
    wph
    @0
    cc
    wcel
    @88
    @84
    adantr
    @93
    @55
    @93
    @54
    @93
    @54
    @95
    nnnn0d
    faccld
    #
    nncnd
    @93
    @55
    @96
    nnne0d
    divcld
    mul01d
    eqtrd
    syl2anc
    eqtr2d
    breqtrd
    pm2.61dan
    pm2.61dan
    dvdsmultr1d
    wph
    @13
    @21
    cJ
    @59
    vj
    @40
    @42
    @21
    @51
    zcnd
    #
    etransclem25.j
    wph
    @3
    cJ
    wceq
    #
    wa
    #
    @14
    @53
    @20
    @58
    cc0
    @98
    @14
    @53
    wb
    wph
    @98
    @4
    @52
    cP
    clt
    @3
    cJ
    cC
    fveq2
    #
    breq2d
    adantl
    @99
    @17
    @56
    @19
    @57
    cmul
    @98
    @17
    @56
    wceq
    wph
    @98
    @16
    @55
    @0
    cdiv
    @98
    @15
    @54
    cfa
    @98
    @4
    @52
    cP
    cmin
    @100
    oveq2d
    #
    fveq2d
    oveq2d
    adantl
    @99
    @18
    cc0
    @15
    @54
    cexp
    @98
    wph
    @18
    @63
    cc0
    @3
    cJ
    cJ
    cmin
    oveq2
    @66
    sylan9eqr
    @98
    @15
    @54
    wceq
    wph
    @101
    adantl
    oveq12d
    oveq12d
    ifbieq2d
    fprodsplit1
    breqtrrd
    @0
    @12
    @22
    dvdsmultr2
    sylc
    wph
    @23
    @7
    @11
    @22
    cmul
    co
    cmul
    co
    cT
    wph
    @7
    @11
    @22
    wph
    @1
    @6
    wph
    @1
    wph
    cN
    etransclem25.n
    faccld
    nncnd
    wph
    @2
    @5
    vj
    @31
    wph
    @44
    wa
    #
    @5
    @102
    @4
    @102
    @32
    cn0
    @4
    @36
    wph
    @2
    @32
    @3
    cC
    etransclem25.c
    ffvelrnda
    sseldi
    faccld
    #
    nncnd
    #
    fprodcl
    wph
    @2
    @5
    vj
    @31
    @104
    @102
    @5
    @103
    nnne0d
    fprodn0
    divcld
    wph
    @11
    @39
    zcnd
    wph
    @13
    @21
    vj
    @40
    @97
    fprodcl
    mulassd
    etransclem25.t
    syl6eqr
    breqtrd
end
