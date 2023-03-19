include "c1.mm"
include "ccom.mm"
include "cvv.mm"
include "cuz.mm"
include "cfv.mm"
include "eqid.mm"
include "nnzd.mm"
include "cc0.mm"
include "cli.mm"
include "wfun.mm"
include "wcel.mm"
include "cc.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c3.mm"
include "cdiv.mm"
include "cmin.mm"
include "funmpt2.mm"
include "cn.mm"
include "cr.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "nnex.mm"
include "fex.mm"
include "sylancl.mm"
include "cofunexg.mm"
include "sylancr.mm"
include "wa.mm"
include "wne.mm"
include "adantr.mm"
include "eluznn.mm"
include "sylan.mm"
include "ffvelrnd.mm"
include "eldifsn.mm"
include "sylib.mm"
include "simpld.mm"
include "recnd.mm"
include "ax-1cn.mm"
include "sqcl.mm"
include "3cn.mm"
include "3ne0.mm"
include "divcl.mm"
include "mp3an23.mm"
include "syl.mm"
include "subcl.mm"
include "fmpti.mm"
include "ccncf.mm"
include "crp.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "cmpt.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "ccn.mm"
include "wtru.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "a1i.mm"
include "1cnd.mm"
include "cnmptc.mm"
include "sqcn.mm"
include "divccn.mm"
include "mp2an.mm"
include "oveq1.mm"
include "cnmpt11.mm"
include "ctx.mm"
include "subcn.mm"
include "cnmpt12f.mm"
include "trud.mm"
include "cncfcn1.mm"
include "3eltr4i.mm"
include "cncfi.mm"
include "mp3an1.mm"
include "wceq.mm"
include "fvco3.mm"
include "syldan.mm"
include "climcn1lem.mm"
include "0cn.mm"
include "sq0i.mm"
include "oveq1d.mm"
include "div0i.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "1m0e1.mm"
include "1ex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "syl6breq.mm"
include "csin.mm"
include "ovex.mm"
include "eqtrd.mm"
include "1re.mm"
include "resqcld.mm"
include "3nn.mm"
include "nndivre.mm"
include "resubcl.mm"
include "eqeltrd.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "resincld.mm"
include "simprd.mm"
include "redivcld.mm"
include "cle.mm"
include "cmul.mm"
include "abscld.mm"
include "subdird.mm"
include "mulid2d.mm"
include "caddc.mm"
include "df-3.mm"
include "oveq2i.mm"
include "cn0.mm"
include "2nn0.mm"
include "expp1.mm"
include "absresq.mm"
include "syl5eq.mm"
include "div23d.mm"
include "eqtr2d.mm"
include "cioc.mm"
include "absrpcld.mm"
include "rpgt0d.mm"
include "ltle.mm"
include "mpd.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "0xr.mm"
include "elioc2.mm"
include "syl3anbrc.mm"
include "sin01bnd.mm"
include "eqbrtrd.mm"
include "ltmuldivd.mm"
include "mpbid.mm"
include "cneg.mm"
include "sinneg.mm"
include "div2negd.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "absord.mm"
include "mpjaod.mm"
include "breqtrd.mm"
include "ltled.mm"
include "3brtr4d.mm"
include "mulid1d.mm"
include "breqtrrd.mm"
include "ltdivmuld.mm"
include "mpbird.mm"
include "eqbrtrrd.mm"
include "climsqz.mm"

theorem sinccvglem
  let wph: wff ph
  let vx: setvar x
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume sinccvg.1: |- ( ph -> F : NN --> ( RR \ { 0 } ) )
  assume sinccvg.2: |- ( ph -> F ~~> 0 )
  assume sinccvg.3: |- G = ( x e. ( RR \ { 0 } ) |-> ( ( sin ` x ) / x ) )
  assume sinccvg.4: |- H = ( x e. CC |-> ( 1 - ( ( x ^ 2 ) / 3 ) ) )
  assume sinccvg.5: |- ( ph -> M e. NN )
  assume sinccvg.6: |- ( ( ph /\ k e. ( ZZ>= ` M ) ) -> ( abs ` ( F ` k ) ) < 1 )

  disjoint k x
  disjoint F k
  disjoint F x
  disjoint H k
  disjoint M k
  disjoint k ph
  disjoint G k
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint H w
  disjoint H y
  disjoint H z
  disjoint M z
  disjoint ph w
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( G o. F ) ~~> 1 )

  proof
    wph
    c1
    vk
    cH
    cF
    ccom
    #
    cG
    cF
    ccom
    #
    cM
    cvv
    cM
    cuz
    cfv
    #
    @2
    eqid
    #
    wph
    cM
    sinccvg.5
    nnzd
    #
    wph
    @0
    cc0
    cH
    cfv
    #
    c1
    cli
    wph
    vy
    vz
    vw
    cc0
    vk
    cF
    @0
    cH
    cM
    cvv
    @2
    @3
    sinccvg.2
    wph
    cH
    wfun
    cF
    cvv
    wcel
    #
    @0
    cvv
    wcel
    vx
    cc
    c1
    vx
    cv
    #
    c2
    cexp
    co
    #
    c3
    cdiv
    co
    #
    cmin
    co
    #
    cH
    sinccvg.4
    funmpt2
    wph
    cn
    cr
    cc0
    csn
    cdif
    #
    cF
    wf
    #
    cn
    cvv
    wcel
    @6
    sinccvg.1
    nnex
    cn
    @11
    cvv
    cF
    fex
    sylancl
    #
    cH
    cF
    cvv
    cofunexg
    sylancr
    @4
    wph
    vk
    cv
    #
    @2
    wcel
    #
    wa
    #
    @14
    cF
    cfv
    #
    @16
    @17
    cr
    wcel
    #
    @17
    cc0
    wne
    #
    @16
    @17
    @11
    wcel
    #
    @18
    @19
    wa
    @16
    cn
    @11
    @14
    cF
    wph
    @12
    @15
    sinccvg.1
    adantr
    wph
    cM
    cn
    wcel
    @15
    @14
    cn
    wcel
    #
    sinccvg.5
    @14
    cM
    eluznn
    sylan
    #
    ffvelrnd
    #
    @17
    cr
    cc0
    eldifsn
    sylib
    #
    simpld
    #
    recnd
    #
    vx
    cc
    cc
    @10
    cH
    sinccvg.4
    @7
    cc
    wcel
    #
    c1
    cc
    wcel
    @9
    cc
    wcel
    #
    @10
    cc
    wcel
    ax-1cn
    @27
    @8
    cc
    wcel
    #
    @28
    @7
    sqcl
    @29
    c3
    cc
    wcel
    #
    c3
    cc0
    wne
    #
    @28
    3cn
    3ne0
    @8
    c3
    divcl
    mp3an23
    syl
    c1
    @9
    subcl
    sylancr
    fmpti
    cH
    cc
    cc
    ccncf
    co
    #
    wcel
    cc0
    cc
    wcel
    #
    vy
    cv
    #
    crp
    wcel
    vw
    cv
    #
    cc0
    cmin
    co
    cabs
    cfv
    vz
    cv
    clt
    wbr
    @35
    cH
    cfv
    @5
    cmin
    co
    cabs
    cfv
    @34
    clt
    wbr
    wi
    vw
    cc
    wral
    vz
    crp
    wrex
    vx
    cc
    @10
    cmpt
    #
    ccnfld
    ctopn
    cfv
    #
    @37
    ccn
    co
    #
    cH
    @32
    @36
    @38
    wcel
    wtru
    vx
    c1
    @9
    cmin
    @37
    @37
    @37
    @37
    cc
    @37
    cc
    ctopon
    cfv
    wcel
    wtru
    @37
    @37
    eqid
    #
    cnfldtopon
    a1i
    #
    wtru
    vx
    c1
    @37
    @37
    cc
    cc
    @40
    @40
    wtru
    1cnd
    cnmptc
    wtru
    vx
    vy
    @8
    @34
    c3
    cdiv
    co
    #
    @9
    @37
    @37
    @37
    cc
    cc
    @40
    vx
    cc
    @8
    cmpt
    @38
    wcel
    wtru
    vx
    @37
    @39
    sqcn
    a1i
    @40
    vy
    cc
    @41
    cmpt
    @38
    wcel
    #
    wtru
    @30
    @31
    @42
    3cn
    3ne0
    vy
    c3
    @37
    @39
    divccn
    mp2an
    a1i
    @34
    @8
    c3
    cdiv
    oveq1
    cnmpt11
    cmin
    @37
    @37
    ctx
    co
    @37
    ccn
    co
    wcel
    wtru
    @37
    @39
    subcn
    a1i
    cnmpt12f
    trud
    sinccvg.4
    @37
    @39
    cncfcn1
    3eltr4i
    vz
    vw
    cc
    cc
    cc0
    @34
    cH
    cncfi
    mp3an1
    wph
    @15
    @21
    @14
    @0
    cfv
    #
    @17
    cH
    cfv
    #
    wceq
    #
    @22
    wph
    @12
    @21
    @45
    sinccvg.1
    cn
    @11
    @14
    cH
    cF
    fvco3
    sylan
    syldan
    #
    climcn1lem
    @33
    @5
    c1
    wceq
    0cn
    vx
    cc0
    @10
    c1
    cc
    cH
    @7
    cc0
    wceq
    #
    @10
    c1
    cc0
    cmin
    co
    c1
    @47
    @9
    cc0
    c1
    cmin
    @47
    @9
    cc0
    c3
    cdiv
    co
    cc0
    @47
    @8
    cc0
    c3
    cdiv
    @7
    sq0i
    oveq1d
    c3
    3cn
    3ne0
    div0i
    syl6eq
    oveq2d
    1m0e1
    syl6eq
    sinccvg.4
    1ex
    fvmpt
    ax-mp
    syl6breq
    wph
    cG
    wfun
    @6
    @1
    cvv
    wcel
    vx
    @11
    @7
    csin
    cfv
    #
    @7
    cdiv
    co
    #
    cG
    sinccvg.3
    funmpt2
    @13
    cG
    cF
    cvv
    cofunexg
    sylancr
    @16
    @43
    c1
    @17
    c2
    cexp
    co
    #
    c3
    cdiv
    co
    #
    cmin
    co
    #
    cr
    @16
    @43
    @44
    @52
    @46
    @16
    @17
    cc
    wcel
    #
    @44
    @52
    wceq
    @26
    vx
    @17
    @10
    @52
    cc
    cH
    @7
    @17
    wceq
    #
    @9
    @51
    c1
    cmin
    @54
    @8
    @50
    c3
    cdiv
    @7
    @17
    c2
    cexp
    oveq1
    oveq1d
    oveq2d
    sinccvg.4
    c1
    @51
    cmin
    ovex
    fvmpt
    syl
    eqtrd
    #
    @16
    c1
    cr
    wcel
    #
    @51
    cr
    wcel
    #
    @52
    cr
    wcel
    1re
    @16
    @50
    cr
    wcel
    c3
    cn
    wcel
    @57
    @16
    @17
    @25
    resqcld
    #
    3nn
    @50
    c3
    nndivre
    sylancl
    #
    c1
    @51
    resubcl
    sylancr
    #
    eqeltrd
    @16
    @14
    @1
    cfv
    #
    @17
    csin
    cfv
    #
    @17
    cdiv
    co
    #
    cr
    @16
    @61
    @17
    cG
    cfv
    #
    @63
    wph
    @15
    @21
    @61
    @64
    wceq
    #
    @22
    wph
    @12
    @21
    @65
    sinccvg.1
    cn
    @11
    @14
    cG
    cF
    fvco3
    sylan
    syldan
    @16
    @20
    @64
    @63
    wceq
    @23
    vx
    @17
    @49
    @63
    @11
    cG
    @54
    @48
    @62
    @7
    @17
    cdiv
    @7
    @17
    csin
    fveq2
    @54
    id
    oveq12d
    sinccvg.3
    @62
    @17
    cdiv
    ovex
    fvmpt
    syl
    eqtrd
    #
    @16
    @62
    @17
    @16
    @17
    @25
    resincld
    #
    @25
    @16
    @18
    @19
    @24
    simprd
    #
    redivcld
    #
    eqeltrd
    @16
    @52
    @63
    @43
    @61
    cle
    @16
    @52
    @63
    @60
    @69
    @16
    @52
    @17
    cabs
    cfv
    #
    csin
    cfv
    #
    @70
    cdiv
    co
    #
    @63
    clt
    @16
    @52
    @70
    cmul
    co
    #
    @71
    clt
    wbr
    @52
    @72
    clt
    wbr
    @16
    @73
    @70
    @70
    c3
    cexp
    co
    #
    c3
    cdiv
    co
    #
    cmin
    co
    #
    @71
    clt
    @16
    @73
    c1
    @70
    cmul
    co
    #
    @51
    @70
    cmul
    co
    #
    cmin
    co
    @76
    @16
    c1
    @51
    @70
    @16
    1cnd
    @16
    @51
    @59
    recnd
    @16
    @70
    @16
    @17
    @26
    abscld
    #
    recnd
    #
    subdird
    @16
    @77
    @70
    @78
    @75
    cmin
    @16
    @70
    @80
    mulid2d
    @16
    @75
    @50
    @70
    cmul
    co
    #
    c3
    cdiv
    co
    @78
    @16
    @74
    @81
    c3
    cdiv
    @16
    @74
    @70
    c2
    c1
    caddc
    co
    #
    cexp
    co
    #
    @81
    c3
    @82
    @70
    cexp
    df-3
    oveq2i
    @16
    @83
    @70
    c2
    cexp
    co
    #
    @70
    cmul
    co
    #
    @81
    @16
    @70
    cc
    wcel
    c2
    cn0
    wcel
    @83
    @85
    wceq
    @80
    2nn0
    @70
    c2
    expp1
    sylancl
    @16
    @84
    @50
    @70
    cmul
    @16
    @18
    @84
    @50
    wceq
    @25
    @17
    absresq
    syl
    oveq1d
    eqtrd
    syl5eq
    oveq1d
    @16
    @50
    @70
    c3
    @16
    @50
    @58
    recnd
    @80
    @30
    @16
    3cn
    a1i
    @31
    @16
    3ne0
    a1i
    div23d
    eqtr2d
    oveq12d
    eqtrd
    @16
    @76
    @71
    clt
    wbr
    #
    @71
    @70
    clt
    wbr
    #
    @16
    @70
    cc0
    c1
    cioc
    co
    wcel
    #
    @86
    @87
    wa
    @16
    @70
    cr
    wcel
    #
    cc0
    @70
    clt
    wbr
    #
    @70
    c1
    cle
    wbr
    #
    @88
    @79
    @16
    @70
    @16
    @17
    @26
    @68
    absrpcld
    #
    rpgt0d
    @16
    @70
    c1
    clt
    wbr
    #
    @91
    sinccvg.6
    @16
    @89
    @56
    @93
    @91
    wi
    @79
    1re
    @70
    c1
    ltle
    sylancl
    mpd
    cc0
    cxr
    wcel
    @56
    @88
    @89
    @90
    @91
    w3a
    wb
    0xr
    1re
    cc0
    c1
    @70
    elioc2
    mp2an
    syl3anbrc
    @70
    sin01bnd
    syl
    #
    simpld
    eqbrtrd
    @16
    @52
    @71
    @70
    @60
    @16
    @70
    @79
    resincld
    #
    @92
    ltmuldivd
    mpbid
    @16
    @70
    @17
    wceq
    #
    @72
    @63
    wceq
    #
    @70
    @17
    cneg
    #
    wceq
    #
    @96
    @97
    wi
    @16
    @96
    @71
    @62
    @70
    @17
    cdiv
    @70
    @17
    csin
    fveq2
    @96
    id
    oveq12d
    a1i
    @16
    @97
    @99
    @98
    csin
    cfv
    #
    @98
    cdiv
    co
    #
    @63
    wceq
    @16
    @101
    @62
    cneg
    #
    @98
    cdiv
    co
    @63
    @16
    @100
    @102
    @98
    cdiv
    @16
    @53
    @100
    @102
    wceq
    @26
    @17
    sinneg
    syl
    oveq1d
    @16
    @62
    @17
    @16
    @62
    @67
    recnd
    @26
    @68
    div2negd
    eqtrd
    @99
    @72
    @101
    @63
    @99
    @71
    @100
    @70
    @98
    cdiv
    @70
    @98
    csin
    fveq2
    @99
    id
    oveq12d
    eqeq1d
    syl5ibrcom
    @16
    @17
    @25
    absord
    mpjaod
    #
    breqtrd
    ltled
    @55
    @66
    3brtr4d
    @16
    @61
    @63
    c1
    cle
    @66
    @16
    @63
    c1
    @69
    @56
    @16
    1re
    a1i
    #
    @16
    @72
    @63
    c1
    clt
    @103
    @16
    @72
    c1
    clt
    wbr
    @71
    @70
    c1
    cmul
    co
    #
    clt
    wbr
    @16
    @71
    @70
    @105
    clt
    @16
    @86
    @87
    @94
    simprd
    @16
    @70
    @80
    mulid1d
    breqtrrd
    @16
    @71
    c1
    @70
    @95
    @104
    @92
    ltdivmuld
    mpbird
    eqbrtrrd
    ltled
    eqbrtrd
    climsqz
end
