include "cvv.mm"
include "cuni.mm"
include "wcel.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "crest.mm"
include "co.mm"
include "cr.mm"
include "cpw.mm"
include "reex.mm"
include "pwex.mm"
include "rabex2.mm"
include "a1i.mm"
include "c0.mm"
include "wa.mm"
include "0elpw.mm"
include "wceq.mm"
include "ima0.mm"
include "csalg.mm"
include "uniexd.mm"
include "smfdmss.mm"
include "ssexd.mm"
include "eqid.mm"
include "subsalsal.mm"
include "0sald.mm"
include "eqeltrd.mm"
include "jca.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "elrab2.mm"
include "sylibr.mm"
include "cdif.mm"
include "wb.mm"
include "wal.mm"
include "nfv.mm"
include "wrex.mm"
include "nfcv.mm"
include "crab.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "eluni2f.mm"
include "biimpi.mm"
include "adantl.mm"
include "nfuni.mm"
include "nfel.mm"
include "nfan.mm"
include "nfel1.mm"
include "wi.mm"
include "wss.mm"
include "eleq2i.mm"
include "rabidim1.mm"
include "syl.mm"
include "elpwi.mm"
include "adantr.mm"
include "simpr.mm"
include "sseldd.mm"
include "ex.mm"
include "rexlimd.mm"
include "mpd.mm"
include "c1.mm"
include "cmin.mm"
include "caddc.mm"
include "cioo.mm"
include "ovexd.mm"
include "ioossre.mm"
include "elpwd.mm"
include "cfv.mm"
include "wfn.mm"
include "smff.mm"
include "ffnd.mm"
include "fncnvima2.mm"
include "wf.mm"
include "ffvelrnd.mm"
include "adantlr.mm"
include "cmpt.mm"
include "csmblfn.mm"
include "feqmptd.mm"
include "eqcomd.mm"
include "cxr.mm"
include "peano2rem.mm"
include "rexrd.mm"
include "peano2re.mm"
include "smfpimioompt.mm"
include "id.mm"
include "ltm1.mm"
include "ltp1.mm"
include "eliood.mm"
include "eleq2.mm"
include "rspcef.mm"
include "syl2anc.mm"
include "impbid.mm"
include "alrimi.mm"
include "dfcleq.mm"
include "difeq1d.mm"
include "difss.mm"
include "ssexi.mm"
include "elpwg.mm"
include "ax-mp.mm"
include "mpbir.mm"
include "wfun.mm"
include "ffund.mm"
include "difpreima.mm"
include "fimacnv.mm"
include "restuni4.mm"
include "eqtr4d.mm"
include "eqtrd.mm"
include "simprd.mm"
include "saldifcld.mm"
include "cn.mm"
include "ciun.mm"
include "nnex.mm"
include "fvex.mm"
include "iunex.mm"
include "ffvelrn.mm"
include "elrabi.mm"
include "iunssd.mm"
include "imaiun.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "nnct.mm"
include "adantll.mm"
include "saliuncl.mm"
include "issalnnd.mm"

theorem smfresal
  let wph: wff ph
  let cD: class D
  let cS: class S
  let cT: class T
  let ve: setvar e
  let cF: class F
  let vn: setvar n
  let vx: setvar x
  let vg: setvar g
  let vy: setvar y
  let vk: setvar k
  assume smfresal.s: |- ( ph -> S e. SAlg )
  assume smfresal.f: |- ( ph -> F e. ( SMblFn ` S ) )
  assume smfresal.d: |- D = dom F
  assume smfresal.t: |- T = { e e. ~P RR | ( `' F " e ) e. ( S |`t D ) }

  disjoint D e
  disjoint F e
  disjoint S e
  disjoint e ph
  disjoint D n
  disjoint D x
  disjoint e n
  disjoint e x
  disjoint n x
  disjoint F n
  disjoint F x
  disjoint S n
  disjoint T g
  disjoint T n
  disjoint T x
  disjoint g n
  disjoint g x
  disjoint T y
  disjoint x y
  disjoint e g
  disjoint g ph
  disjoint n ph
  disjoint ph x
  disjoint e y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> T e. SAlg )

  proof
    wph
    vx
    cT
    vg
    vn
    cvv
    cT
    cuni
    #
    cT
    cvv
    wcel
    wph
    cF
    ccnv
    #
    ve
    cv
    #
    cima
    #
    cS
    cD
    crest
    co
    #
    wcel
    #
    ve
    cr
    cpw
    #
    cT
    smfresal.t
    cr
    reex
    pwex
    rabex2
    a1i
    wph
    c0
    @6
    wcel
    #
    @1
    c0
    cima
    #
    @4
    wcel
    #
    wa
    c0
    cT
    wcel
    wph
    @7
    @9
    @7
    wph
    cr
    0elpw
    a1i
    wph
    @8
    c0
    @4
    @8
    c0
    wceq
    wph
    @1
    ima0
    a1i
    wph
    @4
    wph
    cD
    cS
    @4
    cvv
    smfresal.s
    wph
    cD
    cS
    cuni
    cvv
    wph
    cS
    csalg
    smfresal.s
    uniexd
    wph
    cD
    cS
    cF
    smfresal.s
    smfresal.f
    smfresal.d
    smfdmss
    #
    ssexd
    #
    @4
    eqid
    subsalsal
    #
    0sald
    eqeltrd
    jca
    @5
    @9
    ve
    c0
    @6
    cT
    @2
    c0
    wceq
    @3
    @8
    @4
    @2
    c0
    @1
    imaeq2
    eleq1d
    smfresal.t
    elrab2
    sylibr
    @0
    eqid
    wph
    vx
    cv
    #
    cT
    wcel
    #
    wa
    #
    @0
    @13
    cdif
    #
    cr
    @13
    cdif
    #
    cT
    wph
    @16
    @17
    wceq
    @14
    wph
    @0
    cr
    @13
    wph
    vy
    cv
    #
    @0
    wcel
    #
    @18
    cr
    wcel
    #
    wb
    #
    vy
    wal
    @0
    cr
    wceq
    wph
    @21
    vy
    wph
    vy
    nfv
    wph
    @19
    @20
    wph
    @19
    @20
    wph
    @19
    wa
    #
    @18
    @2
    wcel
    #
    ve
    cT
    wrex
    #
    @20
    @19
    @24
    wph
    @19
    @24
    ve
    @18
    cT
    ve
    @18
    nfcv
    #
    ve
    cT
    @5
    ve
    @6
    crab
    #
    smfresal.t
    @5
    ve
    @6
    nfrab1
    nfcxfr
    #
    eluni2f
    #
    biimpi
    adantl
    @22
    @23
    @20
    ve
    cT
    wph
    @19
    ve
    wph
    ve
    nfv
    ve
    @18
    @0
    @25
    ve
    cT
    @27
    nfuni
    nfel
    nfan
    ve
    @18
    cr
    @25
    nfel1
    @2
    cT
    wcel
    #
    @23
    @20
    wi
    wi
    @22
    @29
    @23
    @20
    @29
    @23
    wa
    @2
    cr
    @18
    @29
    @2
    cr
    wss
    #
    @23
    @29
    @2
    @6
    wcel
    #
    @30
    @29
    @2
    @26
    wcel
    #
    @31
    @29
    @32
    cT
    @26
    @2
    smfresal.t
    eleq2i
    biimpi
    @5
    ve
    @6
    rabidim1
    syl
    @2
    cr
    elpwi
    syl
    adantr
    @29
    @23
    simpr
    sseldd
    ex
    a1i
    rexlimd
    mpd
    ex
    wph
    @20
    @19
    wph
    @20
    wa
    #
    @24
    @19
    @33
    @18
    c1
    cmin
    co
    #
    @18
    c1
    caddc
    co
    #
    cioo
    co
    #
    cT
    wcel
    #
    @18
    @36
    wcel
    #
    @24
    @33
    @36
    @6
    wcel
    #
    @1
    @36
    cima
    #
    @4
    wcel
    #
    wa
    @37
    @33
    @39
    @41
    wph
    @39
    @20
    wph
    @36
    cr
    cvv
    wph
    @34
    @35
    cioo
    ovexd
    @36
    cr
    wss
    wph
    @34
    @35
    ioossre
    a1i
    elpwd
    adantr
    @33
    @40
    @13
    cF
    cfv
    #
    @36
    wcel
    vx
    cD
    crab
    #
    @4
    wph
    @40
    @43
    wceq
    #
    @20
    wph
    cF
    cD
    wfn
    @44
    wph
    cD
    cr
    cF
    wph
    cD
    cS
    cF
    smfresal.s
    smfresal.f
    smfresal.d
    smff
    #
    ffnd
    vx
    cD
    @36
    cF
    fncnvima2
    syl
    adantr
    @33
    vx
    cD
    @42
    @35
    cS
    @34
    cvv
    cr
    @33
    vx
    nfv
    wph
    cS
    csalg
    wcel
    @20
    smfresal.s
    adantr
    wph
    cD
    cvv
    wcel
    @20
    @11
    adantr
    wph
    @13
    cD
    wcel
    #
    @42
    cr
    wcel
    @20
    wph
    @46
    wa
    cD
    cr
    @13
    cF
    wph
    cD
    cr
    cF
    wf
    #
    @46
    @45
    adantr
    wph
    @46
    simpr
    ffvelrnd
    adantlr
    wph
    vx
    cD
    @42
    cmpt
    #
    cS
    csmblfn
    cfv
    #
    wcel
    @20
    wph
    @48
    cF
    @49
    wph
    cF
    @48
    wph
    vx
    cD
    cr
    cF
    @45
    feqmptd
    eqcomd
    smfresal.f
    eqeltrd
    adantr
    @20
    @34
    cxr
    wcel
    wph
    @20
    @34
    @18
    peano2rem
    rexrd
    #
    adantl
    @20
    @35
    cxr
    wcel
    wph
    @20
    @35
    @18
    peano2re
    rexrd
    #
    adantl
    smfpimioompt
    eqeltrd
    jca
    @5
    @41
    ve
    @36
    @6
    cT
    @2
    @36
    wceq
    @3
    @40
    @4
    @2
    @36
    @1
    imaeq2
    eleq1d
    smfresal.t
    elrab2
    sylibr
    @20
    @38
    wph
    @20
    @34
    @35
    @18
    @50
    @51
    @20
    id
    @18
    ltm1
    @18
    ltp1
    eliood
    adantl
    @23
    @38
    ve
    @36
    cT
    @38
    ve
    nfv
    ve
    @36
    nfcv
    @27
    @2
    @36
    @18
    eleq2
    rspcef
    syl2anc
    @28
    sylibr
    ex
    impbid
    alrimi
    vy
    @0
    cr
    dfcleq
    sylibr
    difeq1d
    adantr
    @15
    @17
    @6
    wcel
    #
    @1
    @17
    cima
    #
    @4
    wcel
    #
    wa
    @17
    cT
    wcel
    @15
    @52
    @54
    @52
    @15
    @52
    @17
    cr
    wss
    #
    cr
    @13
    difss
    #
    @17
    cvv
    wcel
    @52
    @55
    wb
    @17
    cr
    reex
    @56
    ssexi
    @17
    cr
    cvv
    elpwg
    ax-mp
    mpbir
    a1i
    @15
    @53
    @4
    cuni
    #
    @1
    @13
    cima
    #
    cdif
    #
    @4
    wph
    @53
    @59
    wceq
    @14
    wph
    @53
    @1
    cr
    cima
    #
    @58
    cdif
    #
    @59
    wph
    cF
    wfun
    @53
    @61
    wceq
    wph
    cD
    cr
    cF
    @45
    ffund
    cr
    @13
    cF
    difpreima
    syl
    wph
    @60
    @57
    @58
    wph
    @60
    cD
    @57
    wph
    @47
    @60
    cD
    wceq
    @45
    cD
    cr
    cF
    fimacnv
    syl
    wph
    cS
    cD
    csalg
    smfresal.s
    @10
    restuni4
    eqtr4d
    difeq1d
    eqtrd
    adantr
    @15
    @4
    @58
    wph
    @4
    csalg
    wcel
    #
    @14
    @12
    adantr
    @14
    @58
    @4
    wcel
    #
    wph
    @14
    @13
    @6
    wcel
    #
    @63
    @14
    @64
    @63
    wa
    @5
    @63
    ve
    @13
    @6
    cT
    @2
    @13
    wceq
    @3
    @58
    @4
    @2
    @13
    @1
    imaeq2
    eleq1d
    smfresal.t
    elrab2
    biimpi
    simprd
    adantl
    saldifcld
    eqeltrd
    jca
    @5
    @54
    ve
    @17
    @6
    cT
    @2
    @17
    wceq
    @3
    @53
    @4
    @2
    @17
    @1
    imaeq2
    eleq1d
    smfresal.t
    elrab2
    sylibr
    eqeltrd
    wph
    cn
    cT
    vg
    cv
    #
    wf
    #
    wa
    #
    vn
    cn
    vn
    cv
    #
    @65
    cfv
    #
    ciun
    #
    @6
    wcel
    #
    @1
    @70
    cima
    #
    @4
    wcel
    #
    wa
    @70
    cT
    wcel
    @67
    @71
    @73
    @66
    @71
    wph
    @66
    @70
    cr
    cvv
    @70
    cvv
    wcel
    @66
    vn
    cn
    @69
    nnex
    @68
    @65
    fvex
    iunex
    a1i
    @66
    vn
    cn
    @69
    cr
    @66
    @68
    cn
    wcel
    #
    wa
    #
    @69
    cT
    wcel
    #
    @69
    cr
    wss
    #
    cn
    cT
    @68
    @65
    ffvelrn
    #
    @76
    @69
    @6
    wcel
    #
    @77
    @76
    @69
    @26
    wcel
    #
    @79
    @76
    @80
    cT
    @26
    @69
    smfresal.t
    eleq2i
    biimpi
    @5
    ve
    @69
    @6
    elrabi
    syl
    @69
    cr
    elpwi
    syl
    syl
    iunssd
    elpwd
    adantl
    @67
    @72
    vn
    cn
    @1
    @69
    cima
    #
    ciun
    #
    @4
    @72
    @82
    wceq
    @67
    vn
    @1
    cn
    @69
    imaiun
    a1i
    @67
    @4
    vn
    @81
    cn
    wph
    @62
    @66
    @12
    adantr
    cn
    com
    cdom
    wbr
    @67
    nnct
    a1i
    @66
    @74
    @81
    @4
    wcel
    #
    wph
    @75
    @76
    @83
    @78
    @76
    @79
    @83
    @76
    @79
    @83
    wa
    @5
    @83
    ve
    @69
    @6
    cT
    @2
    @69
    wceq
    @3
    @81
    @4
    @2
    @69
    @1
    imaeq2
    eleq1d
    smfresal.t
    elrab2
    biimpi
    simprd
    syl
    adantll
    saliuncl
    eqeltrd
    jca
    @5
    @73
    ve
    @70
    @6
    cT
    @2
    @70
    wceq
    @3
    @72
    @4
    @2
    @70
    @1
    imaeq2
    eleq1d
    smfresal.t
    elrab2
    sylibr
    issalnnd
end
