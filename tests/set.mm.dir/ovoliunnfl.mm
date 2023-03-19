include "cn.mm"
include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "cuni.mm"
include "cr.mm"
include "wss.mm"
include "wne.mm"
include "cc0.mm"
include "covol.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "c0.mm"
include "unieq.mm"
include "uni0.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "ovol0.mm"
include "syl6req.mm"
include "a1d.mm"
include "cle.mm"
include "ovolge0.mm"
include "ad2antll.mm"
include "wfo.mm"
include "wex.mm"
include "csdm.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "reldom.mm"
include "brrelexi.mm"
include "0sdomg.mm"
include "syl.mm"
include "biimparc.mm"
include "fodomr.mm"
include "sylancom.mm"
include "unissb.mm"
include "anbi1i.mm"
include "r19.26.mm"
include "bitr4i.mm"
include "cfn.mm"
include "cen.mm"
include "wo.mm"
include "brdom2.mm"
include "com.mm"
include "nnenom.mm"
include "sdomen2.mm"
include "ax-mp.mm"
include "isfinite.mm"
include "orbi1i.mm"
include "bitri.mm"
include "ovolfi.mm"
include "expcom.mm"
include "ovolctb.mm"
include "ex.mm"
include "jaod.mm"
include "syl5bi.mm"
include "imdistani.mm"
include "ralimi.mm"
include "sylbi.mm"
include "ancoms.mm"
include "cima.mm"
include "foima.mm"
include "raleqdv.mm"
include "wfn.mm"
include "fofn.mm"
include "ssid.mm"
include "sseq1.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "ralima.mm"
include "sylancl.mm"
include "bitr3d.mm"
include "ciun.mm"
include "caddc.mm"
include "cmpt.mm"
include "c1.mm"
include "cseq.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "weq.mm"
include "sseq1d.mm"
include "cbvralv.mm"
include "0re.mm"
include "eleq1a.mm"
include "anim2i.mm"
include "syl2an.mm"
include "wfun.mm"
include "fofun.mm"
include "funiunfv.mm"
include "unieqd.mm"
include "eqtrd.mm"
include "adantr.mm"
include "rspccva.mm"
include "simprd.mm"
include "mpteq2dva.mm"
include "seqeq3d.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "csn.mm"
include "cxp.mm"
include "cmul.mm"
include "co.mm"
include "cc.mm"
include "0cn.mm"
include "ser1const.mm"
include "mpan.mm"
include "nncn.mm"
include "mul01d.mm"
include "mpteq2ia.mm"
include "fconstmpt.mm"
include "seqeq3.mm"
include "cuz.mm"
include "cz.mm"
include "1z.mm"
include "seqfn.mm"
include "nnuz.mm"
include "fneq2i.mm"
include "dffn5.mm"
include "bitr3i.mm"
include "mpbi.mm"
include "eqtr3i.mm"
include "3eqtr4i.mm"
include "rneqi.mm"
include "1nn.mm"
include "ne0i.mm"
include "rnxp.mm"
include "mp2b.mm"
include "eqtri.mm"
include "supeq1i.mm"
include "wor.mm"
include "xrltso.mm"
include "0xr.mm"
include "supsn.mm"
include "mp2an.mm"
include "adantl.mm"
include "3brtr3d.mm"
include "sylbid.mm"
include "exlimiv.mm"
include "imp.mm"
include "ovolcl.mm"
include "xrletri3.mm"
include "sylancr.mm"
include "mpbir2and.mm"
include "expl.mm"
include "pm2.61ine.mm"
include "cpnf.mm"
include "renepnf.mm"
include "mp1i.mm"
include "ovolre.mm"
include "neeqtrrd.mm"
include "necon2i.mm"
include "expr.mm"
include "eqimss.mm"
include "necon3bi.mm"
include "pm2.61d1.mm"

theorem ovoliunnfl
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vl: setvar l
  assume ovoliunnfl.0: |- ( ( f Fn NN /\ A. n e. NN ( ( f ` n ) C_ RR /\ ( vol* ` ( f ` n ) ) e. RR ) ) -> ( vol* ` U_ m e. NN ( f ` m ) ) <_ sup ( ran seq 1 ( + , ( m e. NN |-> ( vol* ` ( f ` m ) ) ) ) , RR* , < ) )

  disjoint f n
  disjoint f m
  disjoint f x
  disjoint A f
  disjoint m n
  disjoint n x
  disjoint A n
  disjoint m x
  disjoint A m
  disjoint A x
  disjoint f l
  disjoint l n
  disjoint l m
  disjoint l x
  disjoint A l
  assert |- ( ( A ~<_ NN /\ A. x e. A x ~<_ NN ) -> U. A =/= RR )

  proof
    cA
    cn
    cdom
    wbr
    #
    vx
    cv
    #
    cn
    cdom
    wbr
    #
    vx
    cA
    wral
    #
    wa
    cA
    cuni
    #
    cr
    wss
    #
    @4
    cr
    wne
    #
    @0
    @3
    @5
    @6
    @0
    @3
    @5
    wa
    #
    wa
    #
    cc0
    @4
    covol
    cfv
    #
    wceq
    #
    @6
    @8
    @10
    wi
    cA
    c0
    cA
    c0
    wceq
    #
    @10
    @8
    @11
    @9
    c0
    covol
    cfv
    cc0
    @11
    @4
    c0
    covol
    @11
    @4
    c0
    cuni
    c0
    cA
    c0
    unieq
    uni0
    syl6eq
    fveq2d
    ovol0
    syl6req
    a1d
    cA
    c0
    wne
    #
    @0
    @7
    @10
    @12
    @0
    wa
    #
    @7
    wa
    @10
    cc0
    @9
    cle
    wbr
    #
    @9
    cc0
    cle
    wbr
    #
    @5
    @14
    @13
    @3
    @4
    ovolge0
    ad2antll
    @13
    cn
    cA
    vf
    cv
    #
    wfo
    #
    vf
    wex
    #
    @1
    cr
    wss
    #
    @1
    covol
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vx
    cA
    wral
    #
    @15
    @7
    @12
    @0
    c0
    cA
    csdm
    wbr
    #
    @18
    @0
    @24
    @12
    @0
    cA
    cvv
    wcel
    @24
    @12
    wb
    cA
    cn
    cdom
    reldom
    brrelexi
    cA
    cvv
    0sdomg
    syl
    biimparc
    cn
    cA
    vf
    fodomr
    sylancom
    @5
    @3
    @23
    @5
    @3
    wa
    #
    @19
    @2
    wa
    #
    vx
    cA
    wral
    #
    @23
    @25
    @19
    vx
    cA
    wral
    #
    @3
    wa
    @27
    @5
    @28
    @3
    vx
    cA
    cr
    unissb
    anbi1i
    @19
    @2
    vx
    cA
    r19.26
    bitr4i
    @26
    @22
    vx
    cA
    @19
    @2
    @21
    @2
    @1
    cfn
    wcel
    #
    @1
    cn
    cen
    wbr
    #
    wo
    #
    @19
    @21
    @2
    @1
    cn
    csdm
    wbr
    #
    @30
    wo
    @31
    @1
    cn
    brdom2
    @32
    @29
    @30
    @32
    @1
    com
    csdm
    wbr
    #
    @29
    cn
    com
    cen
    wbr
    @32
    @33
    wb
    nnenom
    cn
    com
    @1
    sdomen2
    ax-mp
    @1
    isfinite
    bitr4i
    orbi1i
    bitri
    @19
    @29
    @21
    @30
    @29
    @19
    @21
    @1
    ovolfi
    expcom
    @19
    @30
    @21
    @1
    ovolctb
    ex
    jaod
    syl5bi
    imdistani
    ralimi
    sylbi
    ancoms
    @18
    @23
    @15
    @17
    @23
    @15
    wi
    vf
    @17
    @23
    vl
    cv
    #
    @16
    cfv
    #
    cr
    wss
    #
    @35
    covol
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vl
    cn
    wral
    #
    @15
    @17
    @22
    vx
    @16
    cn
    cima
    #
    wral
    #
    @23
    @40
    @17
    @22
    vx
    @41
    cA
    cn
    cA
    @16
    foima
    #
    raleqdv
    @17
    @16
    cn
    wfn
    #
    cn
    cn
    wss
    @42
    @40
    wb
    cn
    cA
    @16
    fofn
    #
    cn
    ssid
    @22
    @39
    vx
    vl
    cn
    cn
    @16
    @1
    @35
    wceq
    #
    @19
    @36
    @21
    @38
    @1
    @35
    cr
    sseq1
    @46
    @20
    @37
    cc0
    @1
    @35
    covol
    fveq2
    eqeq1d
    anbi12d
    ralima
    sylancl
    bitr3d
    @17
    @40
    @15
    @17
    @40
    wa
    vm
    cn
    vm
    cv
    #
    @16
    cfv
    #
    ciun
    #
    covol
    cfv
    #
    caddc
    vm
    cn
    @48
    covol
    cfv
    #
    cmpt
    #
    c1
    cseq
    #
    crn
    #
    cxr
    clt
    csup
    #
    @9
    cc0
    cle
    @17
    @44
    vn
    cv
    #
    @16
    cfv
    #
    cr
    wss
    #
    @57
    covol
    cfv
    #
    cr
    wcel
    #
    wa
    #
    vn
    cn
    wral
    #
    @50
    @55
    cle
    wbr
    @40
    @45
    @40
    @58
    @59
    cc0
    wceq
    #
    wa
    #
    vn
    cn
    wral
    @62
    @39
    @64
    vl
    vn
    cn
    vl
    vn
    weq
    #
    @36
    @58
    @38
    @63
    @65
    @35
    @57
    cr
    @34
    @56
    @16
    fveq2
    #
    sseq1d
    @65
    @37
    @59
    cc0
    @65
    @35
    @57
    covol
    @66
    fveq2d
    eqeq1d
    anbi12d
    cbvralv
    @64
    @61
    vn
    cn
    @63
    @60
    @58
    cc0
    cr
    wcel
    #
    @63
    @60
    wi
    0re
    cc0
    cr
    @59
    eleq1a
    ax-mp
    anim2i
    ralimi
    sylbi
    ovoliunnfl.0
    syl2an
    @17
    @50
    @9
    wceq
    @40
    @17
    @49
    @4
    covol
    @17
    @49
    @41
    cuni
    #
    @4
    @17
    @16
    wfun
    @49
    @68
    wceq
    cn
    cA
    @16
    fofun
    vm
    cn
    @16
    funiunfv
    syl
    @17
    @41
    cA
    @43
    unieqd
    eqtrd
    fveq2d
    adantr
    @40
    @55
    cc0
    wceq
    @17
    @40
    @55
    caddc
    vm
    cn
    cc0
    cmpt
    #
    c1
    cseq
    #
    crn
    #
    cxr
    clt
    csup
    #
    cc0
    @40
    cxr
    @54
    @71
    clt
    @40
    @53
    @70
    @40
    @52
    @69
    caddc
    c1
    @40
    vm
    cn
    @51
    cc0
    @40
    @47
    cn
    wcel
    wa
    @48
    cr
    wss
    #
    @51
    cc0
    wceq
    #
    @39
    @73
    @74
    wa
    vl
    @47
    cn
    vl
    vm
    weq
    #
    @36
    @73
    @38
    @74
    @75
    @35
    @48
    cr
    @34
    @47
    @16
    fveq2
    #
    sseq1d
    @75
    @37
    @51
    cc0
    @75
    @35
    @48
    covol
    @76
    fveq2d
    eqeq1d
    anbi12d
    rspccva
    simprd
    mpteq2dva
    seqeq3d
    rneqd
    supeq1d
    @72
    cc0
    csn
    #
    cxr
    clt
    csup
    #
    cc0
    cxr
    @71
    @77
    clt
    @71
    cn
    @77
    cxp
    #
    crn
    #
    @77
    @70
    @79
    vl
    cn
    @34
    caddc
    @79
    c1
    cseq
    #
    cfv
    #
    cmpt
    #
    vl
    cn
    cc0
    cmpt
    @70
    @79
    vl
    cn
    @82
    cc0
    @34
    cn
    wcel
    #
    @82
    @34
    cc0
    cmul
    co
    #
    cc0
    cc0
    cc
    wcel
    @84
    @82
    @85
    wceq
    0cn
    cc0
    @34
    ser1const
    mpan
    @84
    @34
    @34
    nncn
    mul01d
    eqtrd
    mpteq2ia
    @81
    @70
    @83
    @79
    @69
    wceq
    @81
    @70
    wceq
    vm
    cn
    cc0
    fconstmpt
    caddc
    @79
    @69
    c1
    seqeq3
    ax-mp
    @81
    c1
    cuz
    cfv
    #
    wfn
    #
    @81
    @83
    wceq
    #
    c1
    cz
    wcel
    @87
    1z
    caddc
    @79
    c1
    seqfn
    ax-mp
    @87
    @81
    cn
    wfn
    @88
    cn
    @86
    @81
    nnuz
    fneq2i
    vl
    cn
    @81
    dffn5
    bitr3i
    mpbi
    eqtr3i
    vl
    cn
    cc0
    fconstmpt
    3eqtr4i
    rneqi
    c1
    cn
    wcel
    cn
    c0
    wne
    @80
    @77
    wceq
    1nn
    cn
    c1
    ne0i
    cn
    @77
    rnxp
    mp2b
    eqtri
    supeq1i
    cxr
    clt
    wor
    cc0
    cxr
    wcel
    #
    @78
    cc0
    wceq
    xrltso
    0xr
    cxr
    cc0
    clt
    supsn
    mp2an
    eqtri
    syl6eq
    adantl
    3brtr3d
    ex
    sylbid
    exlimiv
    imp
    syl2an
    @5
    @10
    @14
    @15
    wa
    wb
    #
    @13
    @3
    @5
    @89
    @9
    cxr
    wcel
    @90
    0xr
    @4
    ovolcl
    cc0
    @9
    xrletri3
    sylancr
    ad2antll
    mpbir2and
    expl
    pm2.61ine
    @4
    cr
    cc0
    @9
    @4
    cr
    wceq
    #
    cc0
    cpnf
    @9
    @67
    cc0
    cpnf
    wne
    @91
    0re
    cc0
    renepnf
    mp1i
    @91
    @9
    cr
    covol
    cfv
    cpnf
    @4
    cr
    covol
    fveq2
    ovolre
    syl6eq
    neeqtrrd
    necon2i
    syl
    expr
    @5
    @4
    cr
    @4
    cr
    eqimss
    necon3bi
    pm2.61d1
end
