include "cicc.mm"
include "cima.mm"
include "cuni.mm"
include "cvol.mm"
include "cdm.mm"
include "dyadmbllem.mm"
include "com.mm"
include "csdm.mm"
include "wbr.mm"
include "wcel.mm"
include "cen.mm"
include "cfn.mm"
include "isfinite.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "cxr.mm"
include "cxp.mm"
include "cpw.mm"
include "wf.mm"
include "wfun.mm"
include "wceq.mm"
include "iccf.mm"
include "ffun.mm"
include "funiunfv.mm"
include "mp2b.mm"
include "wral.mm"
include "simpr.mm"
include "c1st.mm"
include "c2nd.mm"
include "co.mm"
include "cop.mm"
include "cr.mm"
include "wss.mm"
include "crn.mm"
include "wi.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "syl5ss.mm"
include "cle.mm"
include "cin.mm"
include "cz.mm"
include "cn0.mm"
include "dyadf.mm"
include "frn.mm"
include "ax-mp.mm"
include "inss2.mm"
include "sstri.mm"
include "syl6ss.mm"
include "adantr.mm"
include "sselda.mm"
include "1st2nd2.mm"
include "syl.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "iccmbl.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "finiunmbl.mm"
include "syl5eqelr.mm"
include "sylan2br.mm"
include "cn.mm"
include "wf1o.mm"
include "wex.mm"
include "nnenom.mm"
include "ensym.mm"
include "entr.mm"
include "sylancr.mm"
include "bren.mm"
include "sylib.mm"
include "ccom.mm"
include "rnco2.mm"
include "wfo.mm"
include "f1ofo.mm"
include "adantl.mm"
include "forn.mm"
include "imaeq2d.mm"
include "syl5eq.mm"
include "unieqd.mm"
include "caddc.mm"
include "cabs.mm"
include "cmin.mm"
include "c1.mm"
include "cseq.mm"
include "f1of.mm"
include "fss.mm"
include "syl2anr.mm"
include "cioo.mm"
include "c0.mm"
include "wo.mm"
include "wdisj.mm"
include "w3o.mm"
include "simpl.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "dyaddisj.mm"
include "sseldi.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "elrab2.mm"
include "simprbi.mm"
include "sseq2d.mm"
include "eqeq2.mm"
include "rspcv.mm"
include "sylc.mm"
include "wf1.mm"
include "wb.mm"
include "f1of1.mm"
include "f1fveq.mm"
include "sylan.mm"
include "orc.mm"
include "syl6bi.mm"
include "syld.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "olc.mm"
include "a1i.mm"
include "3jaod.mm"
include "mpd.mm"
include "ralrimivva.mm"
include "disjor.mm"
include "sylibr.mm"
include "eqid.mm"
include "uniiccmbl.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5.mm"
include "imp.mm"
include "cdom.mm"
include "cvv.mm"
include "reex.mm"
include "xpex.mm"
include "inex2.mm"
include "ssexi.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "ccrd.mm"
include "con0.mm"
include "omelon.mm"
include "znnen.mm"
include "entri.mm"
include "nn0ennn.mm"
include "xpen.mm"
include "mp2an.mm"
include "xpomen.mm"
include "ensymi.mm"
include "isnumi.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn4.mm"
include "mpbi.mm"
include "fodomnum.mm"
include "mp2.mm"
include "domentr.mm"
include "domtr.mm"
include "sylancl.mm"
include "brdom2.mm"
include "mpjaodan.mm"

theorem dyadmbl
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cF: class F
  let cG: class G
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let va: setvar a
  let vb: setvar b
  let cB: class B
  let cC: class C
  let vm: setvar m
  let vn: setvar n
  let vt: setvar t
  let vi: setvar i
  let vr: setvar r
  let cD: class D
  assume dyadmbl.1: |- F = ( x e. ZZ , y e. NN0 |-> <. ( x / ( 2 ^ y ) ) , ( ( x + 1 ) / ( 2 ^ y ) ) >. )
  assume dyadmbl.2: |- G = { z e. A | A. w e. A ( ( [,] ` z ) C_ ( [,] ` w ) -> z = w ) }
  assume dyadmbl.3: |- ( ph -> A C_ ran F )

  disjoint x y
  disjoint w z
  disjoint ph w
  disjoint ph z
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint G z
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint c d
  disjoint c f
  disjoint c x
  disjoint c y
  disjoint d f
  disjoint d x
  disjoint d y
  disjoint f x
  disjoint f y
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a x
  disjoint a y
  disjoint B a
  disjoint b c
  disjoint b d
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint a f
  disjoint a m
  disjoint a n
  disjoint a t
  disjoint a w
  disjoint a z
  disjoint a ph
  disjoint b f
  disjoint b m
  disjoint b n
  disjoint b t
  disjoint b w
  disjoint b z
  disjoint b ph
  disjoint f m
  disjoint f n
  disjoint f t
  disjoint f w
  disjoint f z
  disjoint f ph
  disjoint m n
  disjoint m t
  disjoint m w
  disjoint m z
  disjoint m ph
  disjoint n t
  disjoint n w
  disjoint n z
  disjoint n ph
  disjoint t w
  disjoint t z
  disjoint ph t
  disjoint a i
  disjoint a r
  disjoint A a
  disjoint b i
  disjoint b r
  disjoint A b
  disjoint c i
  disjoint c m
  disjoint c n
  disjoint c r
  disjoint c t
  disjoint c w
  disjoint c z
  disjoint A c
  disjoint d i
  disjoint d m
  disjoint d n
  disjoint d r
  disjoint d t
  disjoint d w
  disjoint d z
  disjoint A d
  disjoint i m
  disjoint i n
  disjoint i r
  disjoint i t
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint A i
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint r t
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint D x
  disjoint D y
  disjoint G a
  disjoint G b
  disjoint G f
  disjoint G m
  disjoint G n
  disjoint G t
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F m
  disjoint F n
  disjoint F r
  assert |- ( ph -> U. ( [,] " A ) e. dom vol )

  proof
    wph
    cicc
    cA
    cima
    cuni
    cicc
    cG
    cima
    #
    cuni
    #
    cvol
    cdm
    #
    wph
    vx
    vy
    vz
    vw
    cA
    cF
    cG
    dyadmbl.1
    dyadmbl.2
    dyadmbl.3
    dyadmbllem
    wph
    cG
    com
    csdm
    wbr
    #
    @1
    @2
    wcel
    #
    cG
    com
    cen
    wbr
    #
    @3
    wph
    cG
    cfn
    wcel
    #
    @4
    cG
    isfinite
    wph
    @6
    wa
    #
    @1
    vn
    cG
    vn
    cv
    #
    cicc
    cfv
    #
    ciun
    #
    @2
    cxr
    cxr
    cxp
    #
    cxr
    cpw
    #
    cicc
    wf
    cicc
    wfun
    @10
    @1
    wceq
    iccf
    @11
    @12
    cicc
    ffun
    vn
    cG
    cicc
    funiunfv
    mp2b
    @7
    @6
    @9
    @2
    wcel
    #
    vn
    cG
    wral
    @10
    @2
    wcel
    wph
    @6
    simpr
    @7
    @13
    vn
    cG
    @7
    @8
    cG
    wcel
    wa
    #
    @9
    @8
    c1st
    cfv
    #
    @8
    c2nd
    cfv
    #
    cicc
    co
    #
    @2
    @14
    @9
    @15
    @16
    cop
    #
    cicc
    cfv
    @17
    @14
    @8
    @18
    cicc
    @14
    @8
    cr
    cr
    cxp
    #
    wcel
    #
    @8
    @18
    wceq
    @7
    cG
    @19
    @8
    wph
    cG
    @19
    wss
    @6
    wph
    cG
    cF
    crn
    #
    @19
    wph
    cG
    cA
    @21
    cG
    vz
    cv
    #
    cicc
    cfv
    #
    vw
    cv
    #
    cicc
    cfv
    #
    wss
    #
    @22
    @24
    wceq
    #
    wi
    #
    vw
    cA
    wral
    #
    vz
    cA
    crab
    cA
    dyadmbl.2
    @29
    vz
    cA
    ssrab2
    eqsstri
    #
    dyadmbl.3
    syl5ss
    #
    @21
    cle
    @19
    cin
    #
    @19
    cz
    cn0
    cxp
    #
    @32
    cF
    wf
    #
    @21
    @32
    wss
    vx
    vy
    cF
    dyadmbl.1
    dyadf
    #
    @33
    @32
    cF
    frn
    ax-mp
    #
    cle
    @19
    inss2
    sstri
    syl6ss
    adantr
    sselda
    #
    @8
    cr
    cr
    1st2nd2
    syl
    fveq2d
    @15
    @16
    cicc
    df-ov
    syl6eqr
    @14
    @15
    cr
    wcel
    #
    @16
    cr
    wcel
    #
    @17
    @2
    wcel
    @14
    @20
    @38
    @37
    @8
    cr
    cr
    xp1st
    syl
    @14
    @20
    @39
    @37
    @8
    cr
    cr
    xp2nd
    syl
    @15
    @16
    iccmbl
    syl2anc
    eqeltrd
    ralrimiva
    cG
    @9
    vn
    finiunmbl
    syl2anc
    syl5eqelr
    sylan2br
    wph
    @5
    @4
    @5
    cn
    cG
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    wph
    @4
    @5
    cn
    cG
    cen
    wbr
    #
    @42
    @5
    cn
    com
    cen
    wbr
    com
    cG
    cen
    wbr
    @43
    nnenom
    cG
    com
    ensym
    cn
    com
    cG
    entr
    sylancr
    cn
    cG
    vf
    bren
    sylib
    wph
    @41
    @4
    vf
    wph
    @41
    @4
    wph
    @41
    wa
    #
    cicc
    @40
    ccom
    crn
    #
    cuni
    @1
    @2
    @44
    @45
    @0
    @44
    @45
    cicc
    @40
    crn
    #
    cima
    @0
    cicc
    @40
    rnco2
    @44
    @46
    cG
    cicc
    @44
    cn
    cG
    @40
    wfo
    #
    @46
    cG
    wceq
    @41
    @47
    wph
    cn
    cG
    @40
    f1ofo
    adantl
    cn
    cG
    @40
    forn
    syl
    imaeq2d
    syl5eq
    unieqd
    @44
    va
    caddc
    cabs
    cmin
    ccom
    @40
    ccom
    c1
    cseq
    #
    @40
    @41
    cn
    cG
    @40
    wf
    #
    cG
    @32
    wss
    cn
    @32
    @40
    wf
    wph
    cn
    cG
    @40
    f1of
    #
    wph
    cG
    @21
    @32
    @31
    @36
    syl6ss
    cn
    cG
    @32
    @40
    fss
    syl2anr
    @44
    va
    cv
    #
    vb
    cv
    #
    wceq
    #
    @51
    @40
    cfv
    #
    cioo
    cfv
    #
    @52
    @40
    cfv
    #
    cioo
    cfv
    #
    cin
    c0
    wceq
    #
    wo
    #
    vb
    cn
    wral
    va
    cn
    wral
    va
    cn
    @55
    wdisj
    @44
    @59
    va
    vb
    cn
    cn
    @44
    @51
    cn
    wcel
    #
    @52
    cn
    wcel
    #
    wa
    #
    wa
    #
    @54
    cicc
    cfv
    #
    @56
    cicc
    cfv
    #
    wss
    #
    @65
    @64
    wss
    #
    @58
    w3o
    #
    @59
    @63
    @54
    @21
    wcel
    #
    @56
    @21
    wcel
    #
    @68
    @44
    cn
    @21
    @40
    wf
    #
    @60
    @69
    @62
    @41
    @49
    cG
    @21
    wss
    #
    @71
    wph
    @50
    @31
    cn
    cG
    @21
    @40
    fss
    syl2anr
    #
    @60
    @61
    simpl
    #
    cn
    @21
    @51
    @40
    ffvelrn
    syl2an
    @44
    @71
    @61
    @70
    @62
    @73
    @60
    @61
    simpr
    #
    cn
    @21
    @52
    @40
    ffvelrn
    syl2an
    vx
    vy
    @54
    @56
    cF
    dyadmbl.1
    dyaddisj
    syl2anc
    @63
    @66
    @59
    @67
    @58
    @63
    @66
    @54
    @56
    wceq
    #
    @59
    @63
    @56
    cA
    wcel
    #
    @64
    @25
    wss
    #
    @54
    @24
    wceq
    #
    wi
    #
    vw
    cA
    wral
    #
    @66
    @76
    wi
    #
    @63
    cG
    cA
    @56
    @30
    @44
    @49
    @61
    @56
    cG
    wcel
    #
    @62
    @41
    @49
    wph
    @50
    adantl
    #
    @75
    cn
    cG
    @52
    @40
    ffvelrn
    syl2an
    #
    sseldi
    @63
    @54
    cG
    wcel
    #
    @81
    @44
    @49
    @60
    @86
    @62
    @84
    @74
    cn
    cG
    @51
    @40
    ffvelrn
    syl2an
    #
    @86
    @54
    cA
    wcel
    #
    @81
    @29
    @81
    vz
    @54
    cA
    cG
    @22
    @54
    wceq
    #
    @28
    @80
    vw
    cA
    @89
    @26
    @78
    @27
    @79
    @89
    @23
    @64
    @25
    @22
    @54
    cicc
    fveq2
    sseq1d
    @22
    @54
    @24
    eqeq1
    imbi12d
    ralbidv
    dyadmbl.2
    elrab2
    simprbi
    syl
    @80
    @82
    vw
    @56
    cA
    @24
    @56
    wceq
    #
    @78
    @66
    @79
    @76
    @90
    @25
    @65
    @64
    @24
    @56
    cicc
    fveq2
    sseq2d
    @24
    @56
    @54
    eqeq2
    imbi12d
    rspcv
    sylc
    @63
    @76
    @53
    @59
    @44
    cn
    cG
    @40
    wf1
    #
    @62
    @76
    @53
    wb
    @41
    @91
    wph
    cn
    cG
    @40
    f1of1
    adantl
    cn
    cG
    @51
    @52
    @40
    f1fveq
    sylan
    @53
    @58
    orc
    syl6bi
    #
    syld
    @63
    @67
    @76
    @59
    @63
    @88
    @65
    @25
    wss
    #
    @56
    @24
    wceq
    #
    wi
    #
    vw
    cA
    wral
    #
    @67
    @76
    wi
    #
    @63
    cG
    cA
    @54
    @30
    @87
    sseldi
    @63
    @83
    @96
    @85
    @83
    @77
    @96
    @29
    @96
    vz
    @56
    cA
    cG
    @22
    @56
    wceq
    #
    @28
    @95
    vw
    cA
    @98
    @26
    @93
    @27
    @94
    @98
    @23
    @65
    @25
    @22
    @56
    cicc
    fveq2
    sseq1d
    @22
    @56
    @24
    eqeq1
    imbi12d
    ralbidv
    dyadmbl.2
    elrab2
    simprbi
    syl
    @95
    @97
    vw
    @54
    cA
    @24
    @54
    wceq
    #
    @93
    @67
    @94
    @76
    @99
    @25
    @64
    @65
    @24
    @54
    cicc
    fveq2
    sseq2d
    @99
    @94
    @56
    @54
    wceq
    @76
    @24
    @54
    @56
    eqeq2
    @56
    @54
    eqcom
    syl6bb
    imbi12d
    rspcv
    sylc
    @92
    syld
    @58
    @59
    wi
    @63
    @58
    @53
    olc
    a1i
    3jaod
    mpd
    ralrimivva
    cn
    @55
    @57
    va
    vb
    @53
    @54
    @56
    cioo
    @51
    @52
    @40
    fveq2
    fveq2d
    disjor
    sylibr
    @48
    eqid
    uniiccmbl
    eqeltrrd
    ex
    exlimdv
    syl5
    imp
    wph
    cG
    com
    cdom
    wbr
    #
    @3
    @5
    wo
    wph
    cG
    @21
    cdom
    wbr
    #
    @21
    com
    cdom
    wbr
    #
    @100
    @21
    cvv
    wcel
    wph
    @72
    @101
    @21
    @32
    @19
    cle
    cr
    cr
    reex
    reex
    xpex
    inex2
    @36
    ssexi
    @31
    cG
    @21
    cvv
    ssdomg
    mpsyl
    @21
    @33
    cdom
    wbr
    #
    @33
    com
    cen
    wbr
    @102
    @33
    ccrd
    cdm
    wcel
    #
    @33
    @21
    cF
    wfo
    #
    @103
    com
    con0
    wcel
    com
    @33
    cen
    wbr
    @104
    omelon
    @33
    com
    @33
    com
    com
    cxp
    #
    com
    cz
    com
    cen
    wbr
    cn0
    com
    cen
    wbr
    @33
    @106
    cen
    wbr
    cz
    cn
    com
    znnen
    nnenom
    entri
    cn0
    cn
    com
    nn0ennn
    nnenom
    entri
    cz
    com
    cn0
    com
    xpen
    mp2an
    xpomen
    entri
    #
    ensymi
    com
    @33
    isnumi
    mp2an
    cF
    @33
    wfn
    #
    @105
    @34
    @108
    @35
    @33
    @32
    cF
    ffn
    ax-mp
    @33
    cF
    dffn4
    mpbi
    @33
    @21
    cF
    fodomnum
    mp2
    @107
    @21
    @33
    com
    domentr
    mp2an
    cG
    @21
    com
    domtr
    sylancl
    cG
    com
    brdom2
    sylib
    mpjaodan
    eqeltrd
end
