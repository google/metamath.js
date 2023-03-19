include "cuni.mm"
include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "c2nd.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wbr.mm"
include "cin.mm"
include "wcel.mm"
include "wa.mm"
include "wral.mm"
include "wex.mm"
include "com.mm"
include "cdom.mm"
include "wrex.mm"
include "cn0.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "cvv.mm"
include "wss.mm"
include "nn0ex.mm"
include "fvex.mm"
include "snex.mm"
include "xpex.mm"
include "iunex.mm"
include "c1st.mm"
include "cop.mm"
include "wrel.mm"
include "wceq.mm"
include "w3a.mm"
include "relopabi.mm"
include "1st2nd.mm"
include "mpan.mm"
include "eleq1d.mm"
include "df-br.mm"
include "syl6bbr.mm"
include "heiborlem2.mm"
include "syl6bb.mm"
include "ibi.mm"
include "snid.mm"
include "opelxp.mm"
include "mpbiran2.mm"
include "fveq2.mm"
include "sneq.mm"
include "xpeq12d.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "sylan2br.mm"
include "eliun.mm"
include "sylibr.mm"
include "3adant3.mm"
include "syl.mm"
include "eqeltrd.mm"
include "ssriv.mm"
include "ssdomg.mm"
include "mp2.mm"
include "cen.mm"
include "cn.mm"
include "nn0ennn.mm"
include "nnenom.mm"
include "entri.mm"
include "endom.mm"
include "ax-mp.mm"
include "vex.mm"
include "xpsnen.mm"
include "cfn.mm"
include "cpw.mm"
include "inss2.mm"
include "ffvelrnda.mm"
include "sseldi.mm"
include "csdm.mm"
include "isfinite.mm"
include "sdomdom.mm"
include "sylbi.mm"
include "endomtr.mm"
include "sylancr.mm"
include "ralrimiva.mm"
include "iunctb.mm"
include "domtr.mm"
include "simp1d.mm"
include "peano2nn0.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "iunin2.mm"
include "oveq1.mm"
include "cbviunv.mm"
include "iuneq1d.mm"
include "syl5eq.mm"
include "oveq2.mm"
include "iuneq2d.mm"
include "eqtrd.mm"
include "eqeq2d.mm"
include "rspccva.mm"
include "ineq2d.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "cbl.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "adantl.mm"
include "inss1.mm"
include "elpwid.mm"
include "simp2d.mm"
include "sseldd.mm"
include "oveq2d.mm"
include "ovex.mm"
include "ovmpt2.mm"
include "syl2anc.mm"
include "cxmt.mm"
include "cxr.mm"
include "cme.mm"
include "cms.mm"
include "cmetmet.mm"
include "metxmet.mm"
include "adantr.mm"
include "2nn.mm"
include "nnexpcl.mm"
include "nnrpd.mm"
include "rpreccld.mm"
include "rpxrd.mm"
include "blssm.mm"
include "syl3anc.mm"
include "eqsstrd.mm"
include "df-ss.mm"
include "sylib.mm"
include "eqtr3d.mm"
include "eqimss2.mm"
include "simp3d.mm"
include "inex1.mm"
include "heiborlem1.mm"
include "mopnuni.mm"
include "sseqtrd.mm"
include "sselda.mm"
include "adantrr.mm"
include "id.mm"
include "snfi.mm"
include "unisn.mm"
include "uniiun.mm"
include "eqtr3i.mm"
include "sseqtri.mm"
include "mp3an12.mm"
include "eleq1.mm"
include "rexsn.mm"
include "biimpri.mm"
include "syl3an.mm"
include "3expb.mm"
include "simprr.mm"
include "jca32.mm"
include "ex.mm"
include "reximdv2.mm"
include "mpd.mm"
include "cmopn.mm"
include "eqeltri.mm"
include "uniex.mm"
include "breq1.mm"
include "anbi12d.mm"
include "axcc4dom.mm"
include "exsimpr.mm"

theorem heiborlem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let cB: class B
  let cD: class D
  let cU: class U
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cX: class X
  let vt: setvar t
  let cA: class A
  let vk: setvar k
  let vr: setvar r
  let cM: class M
  let cT: class T
  let wps: wff ps
  let cS: class S
  let cC: class C
  let cY: class Y
  let cZ: class Z
  assume heibor.1: |- J = ( MetOpen ` D )
  assume heibor.3: |- K = { u | -. E. v e. ( ~P U i^i Fin ) u C_ U. v }
  assume heibor.4: |- G = { <. y , n >. | ( n e. NN0 /\ y e. ( F ` n ) /\ ( y B n ) e. K ) }
  assume heibor.5: |- B = ( z e. X , m e. NN0 |-> ( z ( ball ` D ) ( 1 / ( 2 ^ m ) ) ) )
  assume heibor.6: |- ( ph -> D e. ( CMet ` X ) )
  assume heibor.7: |- ( ph -> F : NN0 --> ( ~P X i^i Fin ) )
  assume heibor.8: |- ( ph -> A. n e. NN0 X = U_ y e. ( F ` n ) ( y B n ) )

  disjoint B x
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint n u
  disjoint F n
  disjoint u x
  disjoint u y
  disjoint F u
  disjoint F x
  disjoint F y
  disjoint g x
  disjoint G g
  disjoint G x
  disjoint g ph
  disjoint ph x
  disjoint g m
  disjoint g n
  disjoint g u
  disjoint g v
  disjoint g y
  disjoint g z
  disjoint D g
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint D m
  disjoint n v
  disjoint n z
  disjoint D n
  disjoint u v
  disjoint u z
  disjoint D u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint D v
  disjoint x z
  disjoint D x
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint B g
  disjoint B n
  disjoint B u
  disjoint B v
  disjoint B y
  disjoint J g
  disjoint J m
  disjoint J n
  disjoint J u
  disjoint J v
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint U g
  disjoint U n
  disjoint U u
  disjoint U v
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint X g
  disjoint X m
  disjoint X n
  disjoint X u
  disjoint X v
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint K g
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint n t
  disjoint A n
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint A x
  disjoint A y
  disjoint k n
  disjoint k r
  disjoint k t
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint F k
  disjoint n r
  disjoint r t
  disjoint r u
  disjoint r x
  disjoint r y
  disjoint F r
  disjoint t u
  disjoint F t
  disjoint g k
  disjoint g t
  disjoint G k
  disjoint G t
  disjoint g r
  disjoint k ph
  disjoint ph r
  disjoint ph t
  disjoint k m
  disjoint k v
  disjoint k z
  disjoint D k
  disjoint m r
  disjoint m t
  disjoint r v
  disjoint r z
  disjoint D r
  disjoint t v
  disjoint t z
  disjoint D t
  disjoint M g
  disjoint M k
  disjoint M m
  disjoint M r
  disjoint M t
  disjoint M u
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint T m
  disjoint T n
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint B t
  disjoint J k
  disjoint J r
  disjoint J t
  disjoint U t
  disjoint g ps
  disjoint ps t
  disjoint ps y
  disjoint ps z
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint X k
  disjoint X r
  disjoint X t
  disjoint C m
  disjoint C n
  disjoint C t
  disjoint C u
  disjoint C v
  disjoint C y
  disjoint K t
  disjoint Y k
  disjoint Y t
  disjoint Y x
  disjoint Z k
  disjoint Z v
  disjoint Z x
  assert |- ( ph -> E. g A. x e. G ( ( g ` x ) G ( ( 2nd ` x ) + 1 ) /\ ( ( B ` x ) i^i ( ( g ` x ) B ( ( 2nd ` x ) + 1 ) ) ) e. K ) )

  proof
    wph
    cG
    cJ
    cuni
    #
    vg
    cv
    #
    wf
    #
    vx
    cv
    #
    @1
    cfv
    #
    @3
    c2nd
    cfv
    #
    c1
    caddc
    co
    #
    cG
    wbr
    #
    @3
    cB
    cfv
    #
    @4
    @6
    cB
    co
    #
    cin
    #
    cK
    wcel
    #
    wa
    #
    vx
    cG
    wral
    #
    wa
    vg
    wex
    #
    @13
    vg
    wex
    wph
    cG
    com
    cdom
    wbr
    #
    vt
    cv
    #
    @6
    cG
    wbr
    #
    @8
    @16
    @6
    cB
    co
    #
    cin
    #
    cK
    wcel
    #
    wa
    #
    vt
    @0
    wrex
    #
    vx
    cG
    wral
    @14
    wph
    cG
    vt
    cn0
    @16
    cF
    cfv
    #
    @16
    csn
    #
    cxp
    #
    ciun
    #
    cdom
    wbr
    #
    @26
    com
    cdom
    wbr
    #
    @15
    @26
    cvv
    wcel
    cG
    @26
    wss
    @27
    vt
    cn0
    @25
    nn0ex
    @23
    @24
    @16
    cF
    fvex
    #
    @16
    snex
    xpex
    iunex
    vx
    cG
    @26
    @3
    cG
    wcel
    #
    @3
    @3
    c1st
    cfv
    #
    @5
    cop
    #
    @26
    cG
    wrel
    @30
    @3
    @32
    wceq
    vn
    cv
    #
    cn0
    wcel
    vy
    cv
    #
    @33
    cF
    cfv
    #
    wcel
    @34
    @33
    cB
    co
    #
    cK
    wcel
    w3a
    vy
    vn
    cG
    heibor.4
    relopabi
    @3
    cG
    1st2nd
    mpan
    #
    @30
    @5
    cn0
    wcel
    #
    @31
    @5
    cF
    cfv
    #
    wcel
    #
    @31
    @5
    cB
    co
    #
    cK
    wcel
    #
    w3a
    #
    @32
    @26
    wcel
    #
    @30
    @43
    @30
    @30
    @31
    @5
    cG
    wbr
    #
    @43
    @30
    @30
    @32
    cG
    wcel
    @45
    @30
    @3
    @32
    cG
    @37
    eleq1d
    @31
    @5
    cG
    df-br
    syl6bbr
    vy
    vv
    vu
    @31
    cB
    @5
    cD
    cU
    vn
    cF
    cG
    cJ
    cK
    heibor.1
    heibor.3
    heibor.4
    @3
    c1st
    fvex
    @3
    c2nd
    fvex
    #
    heiborlem2
    syl6bb
    ibi
    #
    @38
    @40
    @44
    @42
    @38
    @40
    wa
    @32
    @25
    wcel
    #
    vt
    cn0
    wrex
    #
    @44
    @40
    @38
    @32
    @39
    @5
    csn
    #
    cxp
    #
    wcel
    #
    @49
    @52
    @40
    @5
    @50
    wcel
    @5
    @46
    snid
    @31
    @5
    @39
    @50
    opelxp
    mpbiran2
    @48
    @52
    vt
    @5
    cn0
    @16
    @5
    wceq
    #
    @25
    @51
    @32
    @53
    @23
    @39
    @24
    @50
    @16
    @5
    cF
    fveq2
    @16
    @5
    sneq
    xpeq12d
    eleq2d
    rspcev
    sylan2br
    vt
    @32
    cn0
    @25
    eliun
    sylibr
    3adant3
    syl
    eqeltrd
    ssriv
    cG
    @26
    cvv
    ssdomg
    mp2
    wph
    cn0
    com
    cdom
    wbr
    #
    @25
    com
    cdom
    wbr
    #
    vt
    cn0
    wral
    @28
    cn0
    com
    cen
    wbr
    @54
    cn0
    cn
    com
    nn0ennn
    nnenom
    entri
    cn0
    com
    endom
    ax-mp
    wph
    @55
    vt
    cn0
    wph
    @16
    cn0
    wcel
    wa
    #
    @25
    @23
    cen
    wbr
    @23
    com
    cdom
    wbr
    #
    @55
    @23
    @16
    @29
    vt
    vex
    #
    xpsnen
    @56
    @23
    cfn
    wcel
    #
    @57
    @56
    cX
    cpw
    #
    cfn
    cin
    #
    cfn
    @23
    @60
    cfn
    inss2
    #
    wph
    cn0
    @61
    @16
    cF
    heibor.7
    ffvelrnda
    sseldi
    @59
    @23
    com
    csdm
    wbr
    @57
    @23
    isfinite
    @23
    com
    sdomdom
    sylbi
    syl
    @25
    @23
    com
    endomtr
    sylancr
    ralrimiva
    vt
    cn0
    @25
    iunctb
    sylancr
    cG
    @26
    com
    domtr
    sylancr
    wph
    @22
    vx
    cG
    wph
    @30
    wa
    #
    @20
    vt
    @6
    cF
    cfv
    #
    wrex
    #
    @22
    @63
    @64
    cfn
    wcel
    @8
    vt
    @64
    @19
    ciun
    #
    wss
    #
    @8
    cK
    wcel
    #
    @65
    @63
    @61
    cfn
    @64
    @62
    wph
    cn0
    @61
    cF
    wf
    #
    @6
    cn0
    wcel
    #
    @64
    @61
    wcel
    @30
    heibor.7
    @30
    @38
    @70
    @30
    @38
    @40
    @42
    @47
    simp1d
    #
    @5
    peano2nn0
    syl
    #
    cn0
    @61
    @6
    cF
    ffvelrn
    syl2an
    #
    sseldi
    @63
    @66
    @8
    wceq
    @67
    @63
    @66
    @8
    vt
    @64
    @18
    ciun
    #
    cin
    #
    @8
    vt
    @64
    @8
    @18
    iunin2
    @63
    @8
    cX
    cin
    #
    @75
    @8
    @63
    cX
    @74
    @8
    wph
    cX
    vy
    @35
    @36
    ciun
    #
    wceq
    #
    vn
    cn0
    wral
    @70
    cX
    @74
    wceq
    #
    @30
    heibor.8
    @72
    @78
    @79
    vn
    @6
    cn0
    @33
    @6
    wceq
    #
    @77
    @74
    cX
    @80
    @77
    vt
    @64
    @16
    @33
    cB
    co
    #
    ciun
    #
    @74
    @80
    @77
    vt
    @35
    @81
    ciun
    @82
    vy
    vt
    @35
    @36
    @81
    @34
    @16
    @33
    cB
    oveq1
    cbviunv
    @80
    vt
    @35
    @64
    @81
    @33
    @6
    cF
    fveq2
    iuneq1d
    syl5eq
    @80
    vt
    @64
    @81
    @18
    @33
    @6
    @16
    cB
    oveq2
    iuneq2d
    eqtrd
    eqeq2d
    rspccva
    syl2an
    ineq2d
    @63
    @8
    cX
    wss
    @76
    @8
    wceq
    @63
    @8
    @31
    c1
    c2
    @5
    cexp
    co
    #
    cdiv
    co
    #
    cD
    cbl
    cfv
    #
    co
    #
    cX
    @63
    @8
    @41
    @86
    @30
    @8
    @41
    wceq
    wph
    @30
    @8
    @32
    cB
    cfv
    @41
    @30
    @3
    @32
    cB
    @37
    fveq2d
    @31
    @5
    cB
    df-ov
    syl6eqr
    #
    adantl
    @63
    @31
    cX
    wcel
    #
    @38
    @41
    @86
    wceq
    @63
    @39
    cX
    @31
    @63
    @39
    cX
    @63
    @61
    @60
    @39
    @60
    cfn
    inss1
    #
    wph
    @69
    @38
    @39
    @61
    wcel
    @30
    heibor.7
    @71
    cn0
    @61
    @5
    cF
    ffvelrn
    syl2an
    sseldi
    elpwid
    @30
    @40
    wph
    @30
    @38
    @40
    @42
    @47
    simp2d
    adantl
    sseldd
    #
    @30
    @38
    wph
    @71
    adantl
    #
    vz
    vm
    @31
    @5
    cX
    cn0
    vz
    cv
    #
    c1
    c2
    vm
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    @85
    co
    @86
    cB
    @31
    @95
    @85
    co
    @92
    @31
    @95
    @85
    oveq1
    @93
    @5
    wceq
    #
    @95
    @84
    @31
    @85
    @96
    @94
    @83
    c1
    cdiv
    @93
    @5
    c2
    cexp
    oveq2
    oveq2d
    oveq2d
    heibor.5
    @31
    @84
    @85
    ovex
    ovmpt2
    syl2anc
    eqtrd
    @63
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @88
    @84
    cxr
    wcel
    @86
    cX
    wss
    wph
    @97
    @30
    wph
    cD
    cX
    cme
    cfv
    wcel
    #
    @97
    wph
    cD
    cX
    cms
    cfv
    wcel
    @98
    heibor.6
    cD
    cX
    cmetmet
    syl
    cD
    cX
    metxmet
    syl
    #
    adantr
    @90
    @63
    @84
    @63
    @83
    @63
    @83
    @63
    c2
    cn
    wcel
    @38
    @83
    cn
    wcel
    2nn
    @91
    c2
    @5
    nnexpcl
    sylancr
    nnrpd
    rpreccld
    rpxrd
    cD
    @31
    @84
    cX
    blssm
    syl3anc
    eqsstrd
    @8
    cX
    df-ss
    sylib
    eqtr3d
    syl5eq
    @8
    @66
    eqimss2
    syl
    @30
    @68
    wph
    @30
    @8
    @41
    cK
    @87
    @30
    @38
    @40
    @42
    @47
    simp3d
    eqeltrd
    adantl
    vt
    vv
    vu
    @64
    @19
    @8
    cD
    cU
    cJ
    cK
    heibor.1
    heibor.3
    @8
    @18
    @3
    cB
    fvex
    inex1
    heiborlem1
    syl3anc
    @63
    @20
    @21
    vt
    @64
    @0
    @63
    @16
    @64
    wcel
    #
    @20
    wa
    #
    @16
    @0
    wcel
    #
    @21
    wa
    @63
    @101
    wa
    @102
    @17
    @20
    @63
    @100
    @102
    @20
    @63
    @64
    @0
    @16
    @63
    @64
    cX
    @0
    @63
    @64
    cX
    @63
    @61
    @60
    @64
    @89
    @73
    sseldi
    elpwid
    wph
    cX
    @0
    wceq
    #
    @30
    wph
    @97
    @103
    @99
    cD
    cJ
    cX
    heibor.1
    mopnuni
    syl
    adantr
    sseqtrd
    sselda
    adantrr
    @63
    @100
    @20
    @17
    @63
    @70
    @100
    @100
    @20
    @18
    cK
    wcel
    #
    @17
    @30
    @70
    wph
    @72
    adantl
    @100
    id
    @20
    @1
    cK
    wcel
    #
    vg
    @18
    csn
    #
    wrex
    #
    @104
    @106
    cfn
    wcel
    @19
    vg
    @106
    @1
    ciun
    #
    wss
    @20
    @107
    @18
    snfi
    @19
    @18
    @108
    @8
    @18
    inss2
    @106
    cuni
    @18
    @108
    @18
    @16
    @6
    cB
    ovex
    #
    unisn
    vg
    @106
    uniiun
    eqtr3i
    sseqtri
    vg
    vv
    vu
    @106
    @1
    @19
    cD
    cU
    cJ
    cK
    heibor.1
    heibor.3
    vg
    vex
    heiborlem1
    mp3an12
    @105
    @104
    vg
    @18
    @109
    @1
    @18
    cK
    eleq1
    rexsn
    sylib
    @17
    @70
    @100
    @104
    w3a
    vy
    vv
    vu
    @16
    cB
    @6
    cD
    cU
    vn
    cF
    cG
    cJ
    cK
    heibor.1
    heibor.3
    heibor.4
    @58
    @5
    c1
    caddc
    ovex
    heiborlem2
    biimpri
    syl3an
    3expb
    @63
    @100
    @20
    simprr
    jca32
    ex
    reximdv2
    mpd
    ralrimiva
    @21
    @12
    vt
    @0
    vg
    vx
    cG
    cJ
    cJ
    cD
    cmopn
    cfv
    cvv
    heibor.1
    cD
    cmopn
    fvex
    eqeltri
    uniex
    @16
    @4
    wceq
    #
    @17
    @7
    @20
    @11
    @16
    @4
    @6
    cG
    breq1
    @110
    @19
    @10
    cK
    @110
    @18
    @9
    @8
    @16
    @4
    @6
    cB
    oveq1
    ineq2d
    eleq1d
    anbi12d
    axcc4dom
    syl2anc
    @2
    @13
    vg
    exsimpr
    syl
end
