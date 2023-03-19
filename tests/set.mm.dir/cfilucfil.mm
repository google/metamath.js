include "c0.mm"
include "wne.mm"
include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "cfg.mm"
include "co.mm"
include "ccfilu.mm"
include "cfbas.mm"
include "cv.mm"
include "cima.mm"
include "cc0.mm"
include "cico.mm"
include "wss.mm"
include "wrex.mm"
include "crp.mm"
include "wral.mm"
include "cust.mm"
include "metust.mm"
include "cfilufbas.mm"
include "sylan.mm"
include "wfun.mm"
include "ccnv.mm"
include "cxr.mm"
include "wf.mm"
include "simpllr.mm"
include "psmetf.mm"
include "ffun.mm"
include "3syl.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "metustfbas.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wceq.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "c2.mm"
include "cdiv.mm"
include "simpr.mm"
include "rphalfcld.mm"
include "eqidd.mm"
include "oveq2.mm"
include "imaeq2d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "metustel.mm"
include "biimpar.mm"
include "cle.mm"
include "wbr.mm"
include "0xr.mm"
include "a1i.mm"
include "rpxr.mm"
include "0le0.mm"
include "rpre.mm"
include "rehalfcld.mm"
include "rphalflt.mm"
include "ltled.mm"
include "icossico.mm"
include "syl22anc.mm"
include "imass2.mm"
include "sseq1.mm"
include "elfg.mm"
include "syl12anc.mm"
include "cfiluexsm.mm"
include "syl3anc.mm"
include "funimass2.mm"
include "ex.mm"
include "reximdv.mm"
include "sylc.mm"
include "ralrimiva.mm"
include "jca.mm"
include "simprl.mm"
include "simp-4r.mm"
include "simprd.mm"
include "sseq2d.mm"
include "rexbidv.mm"
include "rspccv.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfre1.mm"
include "nfral.mm"
include "nfan.mm"
include "ad4antr.mm"
include "fbelss.mm"
include "sylancom.mm"
include "xpss12.mm"
include "simp-6r.mm"
include "sseqtr4d.mm"
include "ralrimi.mm"
include "r19.29r.mm"
include "cin.mm"
include "sseqin2.mm"
include "biimpi.mm"
include "adantl.mm"
include "dminss.mm"
include "syl6eqssr.mm"
include "adantr.mm"
include "sstrd.mm"
include "reximi.mm"
include "syl.mm"
include "r19.41v.mm"
include "sstr.mm"
include "sylbir.mm"
include "simp-5r.mm"
include "biimpa.mm"
include "r19.29a.mm"
include "wb.mm"
include "iscfilu.mm"
include "mpbir2and.mm"
include "impbida.mm"

theorem cfilucfil
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let cF: class F
  let cX: class X
  let va: setvar a
  let cB: class B
  let vb: setvar b
  let cA: class A
  let vp: setvar p
  let vq: setvar q
  let vz: setvar z
  let vr: setvar r
  let vv: setvar v
  let vu: setvar u
  let vw: setvar w
  assume metust.1: |- F = ran ( a e. RR+ |-> ( `' D " ( 0 [,) a ) ) )

  disjoint D a
  disjoint X a
  disjoint F a
  disjoint a x
  disjoint D x
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint X x
  disjoint X y
  disjoint a y
  disjoint D y
  disjoint C a
  disjoint C x
  disjoint C y
  disjoint B a
  disjoint a b
  disjoint A a
  disjoint A b
  disjoint B b
  disjoint D b
  disjoint F b
  disjoint X b
  disjoint a p
  disjoint a q
  disjoint b p
  disjoint b q
  disjoint p q
  disjoint A p
  disjoint A q
  disjoint p x
  disjoint D p
  disjoint q x
  disjoint D q
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint p y
  disjoint p z
  disjoint F p
  disjoint q y
  disjoint q z
  disjoint F q
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint X p
  disjoint X q
  disjoint X z
  disjoint a r
  disjoint a v
  disjoint p r
  disjoint p v
  disjoint q r
  disjoint q v
  disjoint r v
  disjoint A r
  disjoint A v
  disjoint a u
  disjoint a w
  disjoint r u
  disjoint r w
  disjoint D r
  disjoint u v
  disjoint u w
  disjoint D u
  disjoint v w
  disjoint D v
  disjoint D w
  disjoint F r
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint X r
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint v x
  disjoint v y
  disjoint C v
  disjoint w x
  disjoint w y
  disjoint C w
  assert |- ( ( X =/= (/) /\ D e. ( PsMet ` X ) ) -> ( C e. ( CauFilU ` ( ( X X. X ) filGen F ) ) <-> ( C e. ( fBas ` X ) /\ A. x e. RR+ E. y e. C ( D " ( y X. y ) ) C_ ( 0 [,) x ) ) ) )

  proof
    cX
    c0
    wne
    #
    cD
    cX
    cpsmet
    cfv
    wcel
    #
    wa
    #
    cC
    cX
    cX
    cxp
    #
    cF
    cfg
    co
    #
    ccfilu
    cfv
    wcel
    #
    cC
    cX
    cfbas
    cfv
    wcel
    #
    cD
    vy
    cv
    #
    @7
    cxp
    #
    cima
    #
    cc0
    vx
    cv
    #
    cico
    co
    #
    wss
    #
    vy
    cC
    wrex
    #
    vx
    crp
    wral
    #
    wa
    #
    @2
    @5
    wa
    #
    @6
    @14
    @2
    @4
    cX
    cust
    cfv
    wcel
    #
    @5
    @6
    cD
    cF
    cX
    va
    metust.1
    metust
    #
    @4
    cC
    cX
    cfilufbas
    sylan
    @16
    @13
    vx
    crp
    @16
    @10
    crp
    wcel
    #
    wa
    #
    cD
    wfun
    #
    @8
    cD
    ccnv
    #
    @11
    cima
    #
    wss
    #
    vy
    cC
    wrex
    #
    @13
    @20
    @1
    @3
    cxr
    cD
    wf
    #
    @21
    @0
    @1
    @5
    @19
    simpllr
    #
    cD
    cX
    psmetf
    #
    @3
    cxr
    cD
    ffun
    3syl
    @20
    @17
    @5
    @23
    @4
    wcel
    #
    @25
    @2
    @17
    @5
    @19
    @18
    ad2antrr
    @2
    @5
    @19
    simplr
    @20
    cF
    @3
    cfbas
    cfv
    wcel
    #
    @23
    @3
    wss
    #
    vw
    cv
    #
    @23
    wss
    #
    vw
    cF
    wrex
    #
    @29
    @2
    @30
    @5
    @19
    cD
    cF
    cX
    va
    metust.1
    metustfbas
    #
    ad2antrr
    @20
    cD
    cdm
    #
    @23
    @3
    cD
    @11
    cnvimass
    @20
    @1
    @26
    @36
    @3
    wceq
    #
    @27
    @28
    @3
    cxr
    cD
    fdm
    #
    3syl
    syl5sseq
    @20
    @22
    cc0
    @10
    c2
    cdiv
    co
    #
    cico
    co
    #
    cima
    #
    cF
    wcel
    #
    @41
    @23
    wss
    #
    @34
    @20
    @1
    @41
    @22
    cc0
    va
    cv
    #
    cico
    co
    #
    cima
    #
    wceq
    #
    va
    crp
    wrex
    #
    @42
    @27
    @20
    @39
    crp
    wcel
    @41
    @41
    wceq
    #
    @48
    @20
    @10
    @16
    @19
    simpr
    #
    rphalfcld
    @20
    @41
    eqidd
    @47
    @49
    va
    @39
    crp
    @44
    @39
    wceq
    #
    @46
    @41
    @41
    @51
    @45
    @40
    @22
    @44
    @39
    cc0
    cico
    oveq2
    imaeq2d
    eqeq2d
    rspcev
    syl2anc
    @1
    @42
    @48
    @41
    cD
    cF
    cX
    va
    metust.1
    metustel
    biimpar
    syl2anc
    @20
    @19
    @40
    @11
    wss
    #
    @43
    @50
    @19
    cc0
    cxr
    wcel
    #
    @10
    cxr
    wcel
    cc0
    cc0
    cle
    wbr
    #
    @39
    @10
    cle
    wbr
    @52
    @53
    @19
    0xr
    a1i
    @10
    rpxr
    @54
    @19
    0le0
    a1i
    @19
    @39
    @10
    @19
    @10
    @10
    rpre
    #
    rehalfcld
    @55
    @10
    rphalflt
    ltled
    cc0
    @10
    cc0
    @39
    icossico
    syl22anc
    @40
    @11
    @22
    imass2
    3syl
    @33
    @43
    vw
    @41
    cF
    @32
    @41
    @23
    sseq1
    rspcev
    syl2anc
    @30
    @29
    @31
    @34
    wa
    vw
    @23
    cF
    @3
    elfg
    biimpar
    syl12anc
    @4
    cC
    @23
    cX
    vy
    cfiluexsm
    syl3anc
    @21
    @24
    @12
    vy
    cC
    @21
    @24
    @12
    @8
    @11
    cD
    funimass2
    ex
    reximdv
    sylc
    ralrimiva
    jca
    @2
    @15
    wa
    #
    @5
    @6
    @8
    vv
    cv
    #
    wss
    #
    vy
    cC
    wrex
    #
    vv
    @4
    wral
    #
    @2
    @6
    @14
    simprl
    #
    @56
    @59
    vv
    @4
    @56
    @57
    @4
    wcel
    #
    wa
    #
    @46
    @57
    wss
    #
    @59
    va
    crp
    @63
    @44
    crp
    wcel
    #
    wa
    #
    @64
    @8
    @46
    wss
    #
    vy
    cC
    wrex
    #
    @59
    @66
    @64
    wa
    #
    @9
    @45
    wss
    #
    vy
    cC
    wrex
    #
    @8
    @36
    wss
    #
    vy
    cC
    wral
    #
    @68
    @69
    @14
    @65
    @71
    @69
    @6
    @14
    @2
    @15
    @62
    @65
    @64
    simp-4r
    simprd
    @63
    @65
    @64
    simplr
    @13
    @71
    vx
    @44
    crp
    @10
    @44
    wceq
    #
    @12
    @70
    vy
    cC
    @74
    @11
    @45
    @9
    @10
    @44
    cc0
    cico
    oveq2
    sseq2d
    rexbidv
    rspccv
    sylc
    @69
    @72
    vy
    cC
    @66
    @64
    vy
    @63
    @65
    vy
    @56
    @62
    vy
    @2
    @15
    vy
    @2
    vy
    nfv
    @6
    @14
    vy
    @6
    vy
    nfv
    @13
    vy
    vx
    crp
    vy
    crp
    nfcv
    @12
    vy
    cC
    nfre1
    nfral
    nfan
    nfan
    @62
    vy
    nfv
    nfan
    @65
    vy
    nfv
    nfan
    @64
    vy
    nfv
    nfan
    @69
    @7
    cC
    wcel
    #
    @72
    @69
    @75
    wa
    #
    @8
    @3
    @36
    @76
    @7
    cX
    wss
    #
    @77
    @8
    @3
    wss
    @69
    @75
    @6
    @77
    @56
    @6
    @62
    @65
    @64
    @75
    @61
    ad4antr
    cX
    cC
    @7
    fbelss
    sylancom
    #
    @78
    @7
    cX
    @7
    cX
    xpss12
    syl2anc
    @76
    @1
    @26
    @37
    @0
    @1
    @15
    @62
    @65
    @64
    @75
    simp-6r
    @28
    @38
    3syl
    sseqtr4d
    ex
    ralrimi
    @71
    @73
    wa
    @70
    @72
    wa
    #
    vy
    cC
    wrex
    @68
    @70
    @72
    vy
    cC
    r19.29r
    @79
    @67
    vy
    cC
    @79
    @8
    @22
    @9
    cima
    #
    @46
    @79
    @8
    @36
    @8
    cin
    #
    @80
    @72
    @81
    @8
    wceq
    #
    @70
    @72
    @82
    @8
    @36
    sseqin2
    biimpi
    adantl
    @8
    cD
    dminss
    syl6eqssr
    @70
    @80
    @46
    wss
    @72
    @9
    @45
    @22
    imass2
    adantr
    sstrd
    reximi
    syl
    syl2anc
    @68
    @64
    wa
    @67
    @64
    wa
    #
    vy
    cC
    wrex
    @59
    @67
    @64
    vy
    cC
    r19.41v
    @83
    @58
    vy
    cC
    @8
    @46
    @57
    sstr
    reximi
    sylbir
    sylancom
    @63
    @32
    @57
    wss
    #
    @64
    va
    crp
    wrex
    #
    vw
    cF
    @63
    @32
    cF
    wcel
    #
    wa
    #
    @84
    @32
    @46
    wceq
    #
    va
    crp
    wrex
    #
    @85
    @87
    @84
    wa
    @1
    @86
    @89
    @0
    @1
    @15
    @62
    @86
    @84
    simp-5r
    @63
    @86
    @84
    simplr
    @1
    @86
    @89
    @32
    cD
    cF
    cX
    va
    metust.1
    metustel
    biimpa
    syl2anc
    @89
    @84
    wa
    @88
    @84
    wa
    #
    va
    crp
    wrex
    @85
    @88
    @84
    va
    crp
    r19.41v
    @90
    @64
    va
    crp
    @88
    @84
    @64
    @32
    @46
    @57
    sseq1
    biimpa
    reximi
    sylbir
    sylancom
    @63
    @57
    @3
    wss
    #
    @84
    vw
    cF
    wrex
    #
    @56
    @62
    @30
    @91
    @92
    wa
    #
    @2
    @30
    @15
    @62
    @35
    ad2antrr
    @30
    @62
    @93
    vw
    @57
    cF
    @3
    elfg
    biimpa
    sylancom
    simprd
    r19.29a
    r19.29a
    ralrimiva
    @56
    @17
    @5
    @6
    @60
    wa
    wb
    @2
    @17
    @15
    @18
    adantr
    vv
    @4
    cC
    cX
    vy
    iscfilu
    syl
    mpbir2and
    impbida
end
