include "crn.mm"
include "cuni.mm"
include "cr.mm"
include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cxp.mm"
include "cmpt.mm"
include "cun.mm"
include "wceq.mm"
include "csigagen.mm"
include "cfv.mm"
include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "dya2iocucvr.mm"
include "sxbrsigalem0.mm"
include "eqtr4i.mm"
include "wrex.mm"
include "vex.mm"
include "xpex.mm"
include "elrnmpt2.mm"
include "wa.mm"
include "simpr.mm"
include "c1st.mm"
include "cres.mm"
include "ccnv.mm"
include "cima.mm"
include "c2nd.mm"
include "cin.mm"
include "cpw.mm"
include "cbrsiga.mm"
include "dya2icobrsiga.mm"
include "brsigasspwrn.mm"
include "sstri.mm"
include "sseli.mm"
include "elpwid.mm"
include "xpinpreima2.mm"
include "syl2an.mm"
include "csiga.mm"
include "wtru.mm"
include "reex.mm"
include "mptex.mm"
include "rnex.mm"
include "unex.mm"
include "a1i.mm"
include "sgsiga.mm"
include "trud.mm"
include "1stpreima.mm"
include "syl.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "c1.mm"
include "caddc.mm"
include "cz.mm"
include "ovex.mm"
include "xpeq1d.mm"
include "cdif.mm"
include "difxp1.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "simpl.mm"
include "zred.mm"
include "crp.mm"
include "2rp.mm"
include "rpexpcld.mm"
include "rerpdivcld.mm"
include "rexrd.mm"
include "1red.mm"
include "readdcld.mm"
include "pnfxr.mm"
include "lep1d.mm"
include "lediv1dd.mm"
include "pnfge.mm"
include "difico.mm"
include "syl32anc.mm"
include "syl5reqr.mm"
include "ssun1.mm"
include "eqid.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "sylancl.mm"
include "elrnmpti.mm"
include "sylibr.mm"
include "sseldi.mm"
include "elsigagen.mm"
include "sylancr.mm"
include "difelsiga.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "adantr.mm"
include "ex.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "2ndpreima.mm"
include "xpeq2d.mm"
include "difxp2.mm"
include "ssun2.mm"
include "adantl.mm"
include "inelsiga.mm"
include "ssriv.mm"
include "sigagenss2.mm"
include "mp3an.mm"

theorem sxbrsigalem2
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cR: class R
  let ve: setvar e
  let vf: setvar f
  let vn: setvar n
  let cI: class I
  let cJ: class J
  let vd: setvar d
  let vy: setvar y
  assume sxbrsiga.0: |- J = ( topGen ` ran (,) )
  assume dya2ioc.1: |- I = ( x e. ZZ , n e. ZZ |-> ( ( x / ( 2 ^ n ) ) [,) ( ( x + 1 ) / ( 2 ^ n ) ) ) )
  assume dya2ioc.2: |- R = ( u e. ran I , v e. ran I |-> ( u X. v ) )

  disjoint e f
  disjoint e n
  disjoint e u
  disjoint e v
  disjoint e x
  disjoint f n
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint n u
  disjoint n v
  disjoint n x
  disjoint u v
  disjoint u x
  disjoint v x
  disjoint I u
  disjoint I v
  disjoint I x
  disjoint J x
  disjoint n x
  disjoint I x
  disjoint u v
  disjoint I u
  disjoint I v
  disjoint u x
  disjoint v x
  disjoint n u
  disjoint n v
  disjoint R n
  disjoint R x
  disjoint J x
  disjoint d e
  disjoint d f
  disjoint d n
  disjoint d u
  disjoint d v
  disjoint d x
  disjoint R d
  disjoint n y
  disjoint u y
  disjoint v y
  disjoint x y
  disjoint R y
  assert |- ( sigaGen ` ran R ) C_ ( sigaGen ` ( ran ( e e. RR |-> ( ( e [,) +oo ) X. RR ) ) u. ran ( f e. RR |-> ( RR X. ( f [,) +oo ) ) ) ) )

  proof
    cR
    crn
    #
    cuni
    #
    ve
    cr
    ve
    cv
    #
    cpnf
    cico
    co
    #
    cr
    cxp
    #
    cmpt
    #
    crn
    #
    vf
    cr
    cr
    vf
    cv
    #
    cpnf
    cico
    co
    #
    cxp
    #
    cmpt
    #
    crn
    #
    cun
    #
    cuni
    #
    wceq
    @0
    @12
    csigagen
    cfv
    #
    wss
    @12
    cvv
    wcel
    #
    @0
    csigagen
    cfv
    @14
    wss
    @1
    cr
    cr
    cxp
    #
    @13
    vx
    vv
    vu
    cR
    vn
    cI
    cJ
    sxbrsiga.0
    dya2ioc.1
    dya2ioc.2
    dya2iocucvr
    ve
    vf
    sxbrsigalem0
    eqtr4i
    vd
    @0
    @14
    vd
    cv
    #
    @0
    wcel
    @17
    vu
    cv
    #
    vv
    cv
    #
    cxp
    #
    wceq
    #
    vv
    cI
    crn
    #
    wrex
    vu
    @22
    wrex
    @17
    @14
    wcel
    #
    vu
    vv
    @22
    @22
    @20
    @17
    cR
    dya2ioc.2
    @18
    @19
    vu
    vex
    vv
    vex
    xpex
    elrnmpt2
    @21
    @23
    vu
    vv
    @22
    @22
    @18
    @22
    wcel
    #
    @19
    @22
    wcel
    #
    wa
    #
    @21
    @23
    @26
    @21
    wa
    @17
    @20
    @14
    @26
    @21
    simpr
    @26
    @20
    @14
    wcel
    @21
    @26
    @20
    c1st
    @16
    cres
    ccnv
    @18
    cima
    #
    c2nd
    @16
    cres
    ccnv
    @19
    cima
    #
    cin
    #
    @14
    @24
    @18
    cr
    wss
    #
    @19
    cr
    wss
    #
    @20
    @29
    wceq
    @25
    @24
    @18
    cr
    @22
    cr
    cpw
    #
    @18
    @22
    cbrsiga
    @32
    vx
    vn
    cI
    cJ
    sxbrsiga.0
    dya2ioc.1
    dya2icobrsiga
    brsigasspwrn
    sstri
    #
    sseli
    elpwid
    #
    @25
    @19
    cr
    @22
    @32
    @19
    @33
    sseli
    elpwid
    #
    @18
    @19
    cr
    cr
    xpinpreima2
    syl2an
    @26
    @14
    csiga
    crn
    cuni
    wcel
    #
    @27
    @14
    wcel
    #
    @28
    @14
    wcel
    #
    @29
    @14
    wcel
    @36
    @26
    @36
    wtru
    @12
    cvv
    @15
    wtru
    @6
    @11
    @5
    ve
    cr
    @4
    reex
    mptex
    rnex
    @10
    vf
    cr
    @9
    reex
    mptex
    rnex
    unex
    #
    a1i
    sgsiga
    trud
    #
    a1i
    @24
    @37
    @25
    @24
    @27
    @18
    cr
    cxp
    #
    @14
    @24
    @30
    @27
    @41
    wceq
    @34
    @18
    cr
    cr
    1stpreima
    syl
    @24
    @18
    vx
    cv
    #
    c2
    vn
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    @42
    c1
    caddc
    co
    #
    @44
    cdiv
    co
    #
    cico
    co
    #
    wceq
    #
    vn
    cz
    wrex
    vx
    cz
    wrex
    @41
    @14
    wcel
    #
    vx
    vn
    cz
    cz
    @48
    @18
    cI
    dya2ioc.1
    @45
    @47
    cico
    ovex
    #
    elrnmpt2
    @49
    @50
    vx
    vn
    cz
    cz
    @42
    cz
    wcel
    #
    @43
    cz
    wcel
    #
    wa
    #
    @49
    @50
    @54
    @49
    wa
    #
    @41
    @48
    cr
    cxp
    #
    @14
    @55
    @18
    @48
    cr
    @54
    @49
    simpr
    xpeq1d
    @54
    @56
    @14
    wcel
    @49
    @54
    @56
    @45
    cpnf
    cico
    co
    #
    cr
    cxp
    #
    @47
    cpnf
    cico
    co
    #
    cr
    cxp
    #
    cdif
    #
    @14
    @54
    @61
    @57
    @59
    cdif
    #
    cr
    cxp
    @56
    @57
    @59
    cr
    difxp1
    @54
    @62
    @48
    cr
    @54
    @45
    cxr
    wcel
    @47
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    @45
    @47
    cle
    wbr
    @47
    cpnf
    cle
    wbr
    #
    @62
    @48
    wceq
    @54
    @45
    @54
    @42
    @44
    @54
    @42
    @52
    @53
    simpl
    zred
    #
    @54
    c2
    @43
    c2
    crp
    wcel
    @54
    2rp
    a1i
    @52
    @53
    simpr
    rpexpcld
    #
    rerpdivcld
    #
    rexrd
    @54
    @47
    @54
    @46
    @44
    @54
    @42
    c1
    @66
    @54
    1red
    readdcld
    #
    @67
    rerpdivcld
    #
    rexrd
    #
    @64
    @54
    pnfxr
    a1i
    @54
    @42
    @46
    @44
    @66
    @69
    @67
    @54
    @42
    @66
    lep1d
    lediv1dd
    @54
    @63
    @65
    @71
    @47
    pnfge
    syl
    @45
    @47
    cpnf
    difico
    syl32anc
    #
    xpeq1d
    syl5reqr
    @54
    @36
    @58
    @14
    wcel
    #
    @60
    @14
    wcel
    #
    @61
    @14
    wcel
    @36
    @54
    @40
    a1i
    #
    @54
    @15
    @58
    @12
    wcel
    @73
    @39
    @54
    @6
    @12
    @58
    @6
    @11
    ssun1
    #
    @54
    @58
    @4
    wceq
    #
    ve
    cr
    wrex
    #
    @58
    @6
    wcel
    @54
    @45
    cr
    wcel
    #
    @58
    @58
    wceq
    #
    @78
    @68
    @58
    eqid
    @77
    @80
    ve
    @45
    cr
    @2
    @45
    wceq
    #
    @4
    @58
    @58
    @81
    @3
    @57
    cr
    @2
    @45
    cpnf
    cico
    oveq1
    xpeq1d
    eqeq2d
    rspcev
    sylancl
    ve
    cr
    @4
    @58
    @5
    @5
    eqid
    #
    @3
    cr
    @2
    cpnf
    cico
    ovex
    reex
    xpex
    #
    elrnmpti
    sylibr
    sseldi
    @12
    @58
    cvv
    elsigagen
    sylancr
    @54
    @15
    @60
    @12
    wcel
    @74
    @39
    @54
    @6
    @12
    @60
    @76
    @54
    @60
    @4
    wceq
    #
    ve
    cr
    wrex
    #
    @60
    @6
    wcel
    @54
    @47
    cr
    wcel
    #
    @60
    @60
    wceq
    #
    @85
    @70
    @60
    eqid
    @84
    @87
    ve
    @47
    cr
    @2
    @47
    wceq
    #
    @4
    @60
    @60
    @88
    @3
    @59
    cr
    @2
    @47
    cpnf
    cico
    oveq1
    xpeq1d
    eqeq2d
    rspcev
    sylancl
    ve
    cr
    @4
    @60
    @5
    @82
    @83
    elrnmpti
    sylibr
    sseldi
    @12
    @60
    cvv
    elsigagen
    sylancr
    @58
    @60
    @14
    difelsiga
    syl3anc
    eqeltrd
    adantr
    eqeltrd
    ex
    rexlimivv
    sylbi
    eqeltrd
    adantr
    @25
    @38
    @24
    @25
    @28
    cr
    @19
    cxp
    #
    @14
    @25
    @31
    @28
    @89
    wceq
    @35
    @19
    cr
    cr
    2ndpreima
    syl
    @25
    @19
    @48
    wceq
    #
    vn
    cz
    wrex
    vx
    cz
    wrex
    @89
    @14
    wcel
    #
    vx
    vn
    cz
    cz
    @48
    @19
    cI
    dya2ioc.1
    @51
    elrnmpt2
    @90
    @91
    vx
    vn
    cz
    cz
    @54
    @90
    @91
    @54
    @90
    wa
    #
    @89
    cr
    @48
    cxp
    #
    @14
    @92
    @19
    @48
    cr
    @54
    @90
    simpr
    xpeq2d
    @54
    @93
    @14
    wcel
    @90
    @54
    @93
    cr
    @57
    cxp
    #
    cr
    @59
    cxp
    #
    cdif
    #
    @14
    @54
    @96
    cr
    @62
    cxp
    @93
    cr
    @57
    @59
    difxp2
    @54
    @62
    @48
    cr
    @72
    xpeq2d
    syl5reqr
    @54
    @36
    @94
    @14
    wcel
    #
    @95
    @14
    wcel
    #
    @96
    @14
    wcel
    @75
    @54
    @15
    @94
    @12
    wcel
    @97
    @39
    @54
    @11
    @12
    @94
    @11
    @6
    ssun2
    #
    @54
    @94
    @9
    wceq
    #
    vf
    cr
    wrex
    #
    @94
    @11
    wcel
    @54
    @79
    @94
    @94
    wceq
    #
    @101
    @68
    @94
    eqid
    @100
    @102
    vf
    @45
    cr
    @7
    @45
    wceq
    #
    @9
    @94
    @94
    @103
    @8
    @57
    cr
    @7
    @45
    cpnf
    cico
    oveq1
    xpeq2d
    eqeq2d
    rspcev
    sylancl
    vf
    cr
    @9
    @94
    @10
    @10
    eqid
    #
    cr
    @8
    reex
    @7
    cpnf
    cico
    ovex
    xpex
    #
    elrnmpti
    sylibr
    sseldi
    @12
    @94
    cvv
    elsigagen
    sylancr
    @54
    @15
    @95
    @12
    wcel
    @98
    @39
    @54
    @11
    @12
    @95
    @99
    @54
    @95
    @9
    wceq
    #
    vf
    cr
    wrex
    #
    @95
    @11
    wcel
    @54
    @86
    @95
    @95
    wceq
    #
    @107
    @70
    @95
    eqid
    @106
    @108
    vf
    @47
    cr
    @7
    @47
    wceq
    #
    @9
    @95
    @95
    @109
    @8
    @59
    cr
    @7
    @47
    cpnf
    cico
    oveq1
    xpeq2d
    eqeq2d
    rspcev
    sylancl
    vf
    cr
    @9
    @95
    @10
    @104
    @105
    elrnmpti
    sylibr
    sseldi
    @12
    @95
    cvv
    elsigagen
    sylancr
    @94
    @95
    @14
    difelsiga
    syl3anc
    eqeltrd
    adantr
    eqeltrd
    ex
    rexlimivv
    sylbi
    eqeltrd
    adantl
    @27
    @28
    @14
    inelsiga
    syl3anc
    eqeltrd
    adantr
    eqeltrd
    ex
    rexlimivv
    sylbi
    ssriv
    @39
    @0
    @12
    cvv
    sigagenss2
    mp3an
end
