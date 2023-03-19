include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "cpw.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wnel.mm"
include "cv.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "cima.mm"
include "cmpt.mm"
include "crn.mm"
include "wa.mm"
include "simpl2.mm"
include "imassrn.mm"
include "frn.mm"
include "syl5ss.mm"
include "syl.mm"
include "wb.mm"
include "simpl3.mm"
include "elpw2g.mm"
include "mpbird.mm"
include "eqid.mm"
include "fmptd.mm"
include "syl5eqss.mm"
include "wceq.mm"
include "a1i.mm"
include "cdm.mm"
include "wfun.mm"
include "cvv.mm"
include "ffun.mm"
include "3ad2ant2.mm"
include "funimaexg.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "3syl.mm"
include "fbasne0.mm"
include "3ad2ant1.mm"
include "eqnetrd.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "sylib.mm"
include "wn.mm"
include "wi.mm"
include "fbelss.mm"
include "ex.mm"
include "0nelfb.mm"
include "eleq1.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "con2d.mm"
include "jcad.mm"
include "fdm.mm"
include "sseq2d.mm"
include "biimpar.mm"
include "sseqin2.mm"
include "eqeq1d.mm"
include "biimpd.mm"
include "con3d.mm"
include "expimpd.mm"
include "eqcom.mm"
include "imadisj.mm"
include "bitri.mm"
include "notbii.mm"
include "syl6ibr.mm"
include "syld.mm"
include "ralrimiv.mm"
include "eleq2i.mm"
include "0ex.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "df-nel.mm"
include "ralnex.mm"
include "3bitr4i.mm"
include "sylibr.mm"
include "vex.mm"
include "imaeq2.mm"
include "cbvmptv.mm"
include "anbi12i.mm"
include "reeanv.mm"
include "bitr4i.mm"
include "fbasssin.mm"
include "3expb.mm"
include "3ad2antl1.mm"
include "adantrr.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "ad2antrl.mm"
include "funimaex.mm"
include "syl5bb.mm"
include "ad2antrr.mm"
include "imass2.mm"
include "ad2antll.mm"
include "inss1.mm"
include "inss2.mm"
include "ssini.mm"
include "ineq12.mm"
include "ad2antlr.mm"
include "syl5sseqr.mm"
include "sstrd.mm"
include "sseq1.mm"
include "syl2anc.mm"
include "adantlrl.mm"
include "rexlimddv.mm"
include "exp32.mm"
include "rexlimdvv.mm"
include "syl5bi.mm"
include "ralrimivv.mm"
include "3jca.mm"
include "isfbas2.mm"
include "3ad2ant3.mm"
include "mpbir2and.mm"

theorem fbasrn
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  assume fbasrn.c: |- C = ran ( x e. B |-> ( F " x ) )

  disjoint B x
  disjoint F x
  disjoint V x
  disjoint X x
  disjoint Y x
  disjoint r s
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r z
  disjoint B r
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s z
  disjoint B s
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u z
  disjoint B u
  disjoint v w
  disjoint v x
  disjoint v z
  disjoint B v
  disjoint w x
  disjoint w z
  disjoint B w
  disjoint x z
  disjoint B z
  disjoint C r
  disjoint C s
  disjoint C u
  disjoint C v
  disjoint C w
  disjoint C z
  disjoint F r
  disjoint F s
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F z
  disjoint V r
  disjoint V s
  disjoint V u
  disjoint V v
  disjoint V w
  disjoint X r
  disjoint X s
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint Y r
  disjoint Y s
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y z
  assert |- ( ( B e. ( fBas ` X ) /\ F : X --> Y /\ Y e. V ) -> C e. ( fBas ` Y ) )

  proof
    cB
    cX
    cfbas
    cfv
    wcel
    #
    cX
    cY
    cF
    wf
    #
    cY
    cV
    wcel
    #
    w3a
    #
    cC
    cY
    cfbas
    cfv
    wcel
    #
    cC
    cY
    cpw
    #
    wss
    #
    cC
    c0
    wne
    #
    c0
    cC
    wnel
    #
    vz
    cv
    #
    vr
    cv
    #
    vs
    cv
    #
    cin
    #
    wss
    #
    vz
    cC
    wrex
    #
    vs
    cC
    wral
    vr
    cC
    wral
    #
    w3a
    #
    @3
    cC
    vx
    cB
    cF
    vx
    cv
    #
    cima
    #
    cmpt
    #
    crn
    #
    @5
    fbasrn.c
    @3
    cB
    @5
    @19
    wf
    @20
    @5
    wss
    @3
    vx
    cB
    @18
    @5
    @19
    @3
    @17
    cB
    wcel
    #
    wa
    #
    @18
    @5
    wcel
    #
    @18
    cY
    wss
    #
    @22
    @1
    @24
    @0
    @1
    @2
    @21
    simpl2
    @1
    @18
    cF
    crn
    cY
    cF
    @17
    imassrn
    cX
    cY
    cF
    frn
    syl5ss
    syl
    @22
    @2
    @23
    @24
    wb
    @0
    @1
    @2
    @21
    simpl3
    @18
    cY
    cV
    elpw2g
    syl
    mpbird
    @19
    eqid
    #
    fmptd
    cB
    @5
    @19
    frn
    syl
    syl5eqss
    @3
    @7
    @8
    @15
    @3
    cC
    @20
    c0
    cC
    @20
    wceq
    @3
    fbasrn.c
    a1i
    @3
    @19
    cdm
    #
    c0
    wne
    @20
    c0
    wne
    @3
    @26
    cB
    c0
    @3
    cF
    wfun
    #
    @18
    cvv
    wcel
    #
    vx
    cB
    wral
    @26
    cB
    wceq
    @1
    @0
    @27
    @2
    cX
    cY
    cF
    ffun
    3ad2ant2
    #
    @27
    @28
    vx
    cB
    cF
    @17
    cB
    funimaexg
    ralrimiva
    vx
    cB
    @18
    cvv
    dmmptg
    3syl
    @0
    @1
    cB
    c0
    wne
    @2
    cX
    cB
    fbasne0
    3ad2ant1
    eqnetrd
    @26
    c0
    @20
    c0
    @19
    dm0rn0
    necon3bii
    sylib
    eqnetrd
    @3
    c0
    @18
    wceq
    #
    wn
    #
    vx
    cB
    wral
    #
    @8
    @3
    @31
    vx
    cB
    @3
    @21
    @17
    cX
    wss
    #
    @17
    c0
    wceq
    #
    wn
    #
    wa
    #
    @31
    @3
    @21
    @33
    @35
    @0
    @1
    @21
    @33
    wi
    @2
    @0
    @21
    @33
    cX
    cB
    @17
    fbelss
    ex
    3ad2ant1
    @0
    @1
    @21
    @35
    wi
    @2
    @0
    @34
    @21
    @0
    @21
    wn
    @34
    c0
    cB
    wcel
    #
    wn
    cX
    cB
    0nelfb
    @34
    @21
    @37
    @17
    c0
    cB
    eleq1
    notbid
    syl5ibrcom
    con2d
    3ad2ant1
    jcad
    @3
    @36
    cF
    cdm
    #
    @17
    cin
    #
    c0
    wceq
    #
    wn
    #
    @31
    @3
    @33
    @35
    @41
    @3
    @33
    wa
    #
    @40
    @34
    @42
    @40
    @34
    @42
    @39
    @17
    c0
    @42
    @17
    @38
    wss
    #
    @39
    @17
    wceq
    @3
    @43
    @33
    @3
    @38
    cX
    @17
    @1
    @0
    @38
    cX
    wceq
    @2
    cX
    cY
    cF
    fdm
    3ad2ant2
    sseq2d
    biimpar
    @17
    @38
    sseqin2
    sylib
    eqeq1d
    biimpd
    con3d
    expimpd
    @30
    @40
    @30
    @18
    c0
    wceq
    @40
    c0
    @18
    eqcom
    cF
    @17
    imadisj
    bitri
    notbii
    syl6ibr
    syld
    ralrimiv
    c0
    cC
    wcel
    #
    wn
    @30
    vx
    cB
    wrex
    #
    wn
    @8
    @32
    @44
    @45
    @44
    c0
    @20
    wcel
    #
    @45
    cC
    @20
    c0
    fbasrn.c
    eleq2i
    c0
    cvv
    wcel
    @46
    @45
    wb
    0ex
    vx
    cB
    @18
    c0
    @19
    cvv
    @25
    elrnmpt
    ax-mp
    bitri
    notbii
    c0
    cC
    df-nel
    @30
    vx
    cB
    ralnex
    3bitr4i
    sylibr
    @3
    @14
    vr
    vs
    cC
    cC
    @10
    cC
    wcel
    #
    @11
    cC
    wcel
    #
    wa
    #
    @10
    cF
    vu
    cv
    #
    cima
    #
    wceq
    #
    @11
    cF
    vv
    cv
    #
    cima
    #
    wceq
    #
    wa
    #
    vv
    cB
    wrex
    vu
    cB
    wrex
    #
    @3
    @14
    @49
    @52
    vu
    cB
    wrex
    #
    @55
    vv
    cB
    wrex
    #
    wa
    @57
    @47
    @58
    @48
    @59
    @47
    @10
    @20
    wcel
    #
    @58
    cC
    @20
    @10
    fbasrn.c
    eleq2i
    @10
    cvv
    wcel
    @60
    @58
    wb
    vr
    vex
    vu
    cB
    @51
    @10
    @19
    cvv
    vx
    vu
    cB
    @18
    @51
    @17
    @50
    cF
    imaeq2
    cbvmptv
    elrnmpt
    ax-mp
    bitri
    @48
    @11
    @20
    wcel
    #
    @59
    cC
    @20
    @11
    fbasrn.c
    eleq2i
    @11
    cvv
    wcel
    @61
    @59
    wb
    vs
    vex
    vv
    cB
    @54
    @11
    @19
    cvv
    vx
    vv
    cB
    @18
    @54
    @17
    @53
    cF
    imaeq2
    cbvmptv
    elrnmpt
    ax-mp
    bitri
    anbi12i
    @52
    @55
    vu
    vv
    cB
    cB
    reeanv
    bitr4i
    @3
    @56
    @14
    vu
    vv
    cB
    cB
    @3
    @50
    cB
    wcel
    #
    @53
    cB
    wcel
    #
    wa
    #
    @56
    @14
    @3
    @64
    @56
    wa
    wa
    vw
    cv
    #
    @50
    @53
    cin
    #
    wss
    #
    @14
    vw
    cB
    @3
    @64
    @67
    vw
    cB
    wrex
    #
    @56
    @0
    @1
    @64
    @68
    @2
    @0
    @62
    @63
    @68
    vw
    @50
    @53
    cB
    cX
    fbasssin
    3expb
    3ad2antl1
    adantrr
    @3
    @56
    @65
    cB
    wcel
    #
    @67
    wa
    #
    @14
    @64
    @3
    @56
    wa
    #
    @70
    wa
    #
    cF
    @65
    cima
    #
    cC
    wcel
    #
    @73
    @12
    wss
    #
    @14
    @72
    @74
    @73
    @18
    wceq
    #
    vx
    cB
    wrex
    #
    @69
    @77
    @71
    @67
    @69
    @73
    @73
    wceq
    #
    @77
    @73
    eqid
    @76
    @78
    vx
    @65
    cB
    @17
    @65
    wceq
    @18
    @73
    @73
    @17
    @65
    cF
    imaeq2
    eqeq2d
    rspcev
    mpan2
    ad2antrl
    @3
    @74
    @77
    wb
    @56
    @70
    @74
    @73
    @20
    wcel
    #
    @3
    @77
    cC
    @20
    @73
    fbasrn.c
    eleq2i
    @3
    @27
    @73
    cvv
    wcel
    @79
    @77
    wb
    @29
    cF
    @65
    vw
    vex
    funimaex
    vx
    cB
    @18
    @73
    @19
    cvv
    @25
    elrnmpt
    3syl
    syl5bb
    ad2antrr
    mpbird
    @72
    @73
    cF
    @66
    cima
    #
    @12
    @67
    @73
    @80
    wss
    @71
    @69
    @65
    @66
    cF
    imass2
    ad2antll
    @72
    @51
    @54
    cin
    #
    @80
    @12
    @80
    @51
    @54
    @66
    @50
    wss
    @80
    @51
    wss
    @50
    @53
    inss1
    @66
    @50
    cF
    imass2
    ax-mp
    @66
    @53
    wss
    @80
    @54
    wss
    @50
    @53
    inss2
    @66
    @53
    cF
    imass2
    ax-mp
    ssini
    @56
    @12
    @81
    wceq
    @3
    @70
    @10
    @51
    @11
    @54
    ineq12
    ad2antlr
    syl5sseqr
    sstrd
    @13
    @75
    vz
    @73
    cC
    @9
    @73
    @12
    sseq1
    rspcev
    syl2anc
    adantlrl
    rexlimddv
    exp32
    rexlimdvv
    syl5bi
    ralrimivv
    3jca
    @2
    @0
    @4
    @6
    @16
    wa
    wb
    @1
    vr
    vs
    vz
    cV
    cY
    cC
    isfbas2
    3ad2ant3
    mpbir2and
end
