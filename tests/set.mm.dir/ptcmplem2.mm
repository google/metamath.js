include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "cuni.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "ciun.mm"
include "ccrd.mm"
include "cdm.mm"
include "c0.mm"
include "wne.mm"
include "wex.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wss.mm"
include "0ss.mm"
include "0fin.mm"
include "elfpw.mm"
include "mpbir2an.mm"
include "unieq.mm"
include "uni0.mm"
include "syl6eq.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan.mm"
include "necon3bi.mm"
include "syl.mm"
include "n0.mm"
include "sylib.mm"
include "wa.mm"
include "cixp.mm"
include "cxp.mm"
include "cwdom.mm"
include "cres.mm"
include "cmpt.mm"
include "wfo.mm"
include "weq.mm"
include "fveq2.mm"
include "unieqd.mm"
include "cbvixpv.mm"
include "eqtri.mm"
include "cufl.mm"
include "inss2.mm"
include "sseldi.mm"
include "adantr.mm"
include "syl5eqelr.mm"
include "ssrab2.mm"
include "syl5eqner.mm"
include "eqid.mm"
include "resixpfo.mm"
include "sylancr.mm"
include "fonum.mm"
include "syl2anc.mm"
include "cdif.mm"
include "crn.mm"
include "wfn.mm"
include "cvv.mm"
include "wral.mm"
include "vex.mm"
include "difexg.mm"
include "mp1i.mm"
include "dmexg.mm"
include "uniexg.mm"
include "3syl.mm"
include "ralrimivw.mm"
include "fnmpt.mm"
include "dffn4.mm"
include "csn.mm"
include "ssdif0.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "elixp.mm"
include "simprbi.mm"
include "r19.21bi.mm"
include "snssd.mm"
include "eqssd.mm"
include "fvex.mm"
include "ensn1.mm"
include "syl6eqbr.mm"
include "ex.mm"
include "syl5bir.mm"
include "con3d.mm"
include "neq0.mm"
include "syl6ib.mm"
include "cif.mm"
include "eldifi.mm"
include "simplr.mm"
include "iftrue.mm"
include "eleq12d.mm"
include "syl5ibrcom.mm"
include "ad2antrr.mm"
include "iffalse.mm"
include "eleq1d.mm"
include "pm2.61d.mm"
include "ralrimiva.mm"
include "wb.mm"
include "ad3antrrr.mm"
include "mptelixpg.mm"
include "mpbird.mm"
include "syl6eleqr.mm"
include "sylan2.mm"
include "unisn.mm"
include "cab.mm"
include "eleq1.mm"
include "pm4.71rd.mm"
include "equequ1.mm"
include "ifbieq2d.mm"
include "ifex.mm"
include "fvmpt.mm"
include "neeq1d.mm"
include "adantl.mm"
include "necon1ai.mm"
include "eldifsni.mm"
include "ad2antlr.mm"
include "neeq12d.mm"
include "impbid2.mm"
include "bitrd.mm"
include "pm5.32da.mm"
include "bitr4d.mm"
include "abbidv.mm"
include "df-sn.mm"
include "df-rab.mm"
include "3eqtr4g.mm"
include "rgenw.mm"
include "ixpfn.mm"
include "fndmdif.mm"
include "eqtr4d.mm"
include "syl5eqr.mm"
include "difeq1.mm"
include "dmeqd.mm"
include "exlimdv.mm"
include "syld.mm"
include "expimpd.mm"
include "breq1d.mm"
include "notbid.mm"
include "elrab.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "3imtr4g.mm"
include "ssrdv.mm"
include "ssnum.mm"
include "xpnum.mm"
include "rabexg.mm"
include "uniex.mm"
include "iunexg.mm"
include "sylancl.mm"
include "resixp.mm"
include "ne0i.mm"
include "ixpiunwdom.mm"
include "syl3anc.mm"
include "numwdom.mm"
include "exlimddv.mm"

theorem ptcmplem2
  let wph: wff ph
  let vz: setvar z
  let vw: setvar w
  let vu: setvar u
  let cA: class A
  let cS: class S
  let cU: class U
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cV: class V
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vt: setvar t
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let cK: class K
  assume ptcmp.1: |- S = ( k e. A , u e. ( F ` k ) |-> ( `' ( w e. X |-> ( w ` k ) ) " u ) )
  assume ptcmp.2: |- X = X_ n e. A U. ( F ` n )
  assume ptcmp.3: |- ( ph -> A e. V )
  assume ptcmp.4: |- ( ph -> F : A --> Comp )
  assume ptcmp.5: |- ( ph -> X e. ( UFL i^i dom card ) )
  assume ptcmplem2.5: |- ( ph -> U C_ ran S )
  assume ptcmplem2.6: |- ( ph -> X = U. U )
  assume ptcmplem2.7: |- ( ph -> -. E. z e. ( ~P U i^i Fin ) X = U. z )

  disjoint k n
  disjoint k u
  disjoint k w
  disjoint k z
  disjoint A k
  disjoint n u
  disjoint n w
  disjoint n z
  disjoint A n
  disjoint u w
  disjoint u z
  disjoint A u
  disjoint w z
  disjoint A w
  disjoint A z
  disjoint S k
  disjoint S n
  disjoint S u
  disjoint S z
  disjoint k ph
  disjoint n ph
  disjoint ph u
  disjoint U k
  disjoint U u
  disjoint U z
  disjoint V k
  disjoint V n
  disjoint V u
  disjoint V w
  disjoint V z
  disjoint F k
  disjoint F n
  disjoint F u
  disjoint F w
  disjoint F z
  disjoint X k
  disjoint X n
  disjoint X u
  disjoint X w
  disjoint X z
  disjoint f g
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint k m
  disjoint k t
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint m n
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n t
  disjoint n v
  disjoint n x
  disjoint n y
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint K f
  disjoint K g
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K x
  disjoint K y
  disjoint S v
  disjoint S y
  disjoint f ph
  disjoint g ph
  disjoint m ph
  disjoint ph t
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint U t
  disjoint U v
  disjoint U x
  disjoint V g
  disjoint V x
  disjoint V y
  disjoint F f
  disjoint F g
  disjoint F m
  disjoint F t
  disjoint F v
  disjoint F x
  disjoint F y
  disjoint X f
  disjoint X g
  disjoint X m
  disjoint X t
  disjoint X v
  disjoint X x
  disjoint X y
  assert |- ( ph -> U_ k e. { n e. A | -. U. ( F ` n ) ~~ 1o } U. ( F ` k ) e. dom card )

  proof
    wph
    vf
    cv
    #
    cX
    wcel
    #
    vk
    vn
    cv
    #
    cF
    cfv
    #
    cuni
    #
    c1o
    cen
    wbr
    #
    wn
    #
    vn
    cA
    crab
    #
    vk
    cv
    #
    cF
    cfv
    #
    cuni
    #
    ciun
    #
    ccrd
    cdm
    #
    wcel
    #
    vf
    wph
    cX
    c0
    wne
    #
    @1
    vf
    wex
    wph
    cX
    vz
    cv
    #
    cuni
    #
    wceq
    #
    vz
    cU
    cpw
    cfn
    cin
    #
    wrex
    #
    wn
    @14
    ptcmplem2.7
    @19
    cX
    c0
    c0
    @18
    wcel
    #
    cX
    c0
    wceq
    #
    @19
    @20
    c0
    cU
    wss
    c0
    cfn
    wcel
    cU
    0ss
    0fin
    c0
    cU
    elfpw
    mpbir2an
    @17
    @21
    vz
    c0
    @18
    @15
    c0
    wceq
    #
    @16
    c0
    cX
    @22
    @16
    c0
    cuni
    c0
    @15
    c0
    unieq
    uni0
    syl6eq
    eqeq2d
    rspcev
    mpan
    necon3bi
    syl
    #
    vf
    cX
    n0
    sylib
    wph
    @1
    wa
    #
    vk
    @7
    @10
    cixp
    #
    @7
    cxp
    #
    @12
    wcel
    #
    @11
    @26
    cwdom
    wbr
    #
    @13
    @24
    @25
    @12
    wcel
    #
    @7
    @12
    wcel
    #
    @27
    @24
    vk
    cA
    @10
    cixp
    #
    @12
    wcel
    @31
    @25
    vg
    @31
    vg
    cv
    #
    @7
    cres
    cmpt
    #
    wfo
    #
    @29
    @24
    @31
    cX
    @12
    cX
    vn
    cA
    @4
    cixp
    #
    @31
    ptcmp.2
    vn
    vk
    cA
    @4
    @10
    vn
    vk
    weq
    #
    @3
    @9
    @2
    @8
    cF
    fveq2
    unieqd
    #
    cbvixpv
    eqtri
    #
    wph
    cX
    @12
    wcel
    #
    @1
    wph
    cufl
    @12
    cin
    @12
    cX
    cufl
    @12
    inss2
    ptcmp.5
    sseldi
    adantr
    #
    syl5eqelr
    @24
    @7
    cA
    wss
    #
    @31
    c0
    wne
    @34
    @6
    vn
    cA
    ssrab2
    #
    @24
    @31
    cX
    c0
    @38
    wph
    @14
    @1
    @23
    adantr
    syl5eqner
    vk
    cA
    @7
    @10
    vg
    @33
    @33
    eqid
    resixpfo
    sylancr
    @31
    @25
    @33
    fonum
    syl2anc
    @24
    vg
    cX
    @32
    @0
    cdif
    #
    cdm
    #
    cuni
    #
    cmpt
    #
    crn
    #
    @12
    wcel
    #
    @7
    @47
    wss
    @30
    @24
    @39
    cX
    @47
    @46
    wfo
    #
    @48
    @40
    @24
    @46
    cX
    wfn
    #
    @49
    @24
    @45
    cvv
    wcel
    #
    vg
    cX
    wral
    @50
    @24
    @51
    vg
    cX
    @24
    @43
    cvv
    wcel
    #
    @44
    cvv
    wcel
    @51
    @32
    cvv
    wcel
    @52
    @24
    vg
    vex
    @32
    @0
    cvv
    difexg
    mp1i
    @43
    cvv
    dmexg
    @44
    cvv
    uniexg
    3syl
    ralrimivw
    vg
    cX
    @45
    @46
    cvv
    @46
    eqid
    #
    fnmpt
    syl
    cX
    @46
    dffn4
    sylib
    cX
    @47
    @46
    fonum
    syl2anc
    @24
    vk
    @7
    @47
    @24
    @8
    cA
    wcel
    #
    @10
    c1o
    cen
    wbr
    #
    wn
    #
    wa
    @8
    @45
    wceq
    #
    vg
    cX
    wrex
    #
    @8
    @7
    wcel
    @8
    @47
    wcel
    #
    @24
    @54
    @56
    @58
    @24
    @54
    wa
    #
    @56
    vx
    cv
    #
    @10
    @8
    @0
    cfv
    #
    csn
    #
    cdif
    #
    wcel
    #
    vx
    wex
    #
    @58
    @60
    @56
    @64
    c0
    wceq
    #
    wn
    @66
    @60
    @67
    @55
    @67
    @10
    @63
    wss
    #
    @60
    @55
    @10
    @63
    ssdif0
    @60
    @68
    @55
    @60
    @68
    wa
    #
    @10
    @63
    c1o
    cen
    @69
    @10
    @63
    @60
    @68
    simpr
    @60
    @63
    @10
    wss
    @68
    @60
    @62
    @10
    @24
    @62
    @10
    wcel
    #
    vk
    cA
    @24
    @0
    @31
    wcel
    #
    @70
    vk
    cA
    wral
    #
    @24
    @0
    cX
    @31
    wph
    @1
    simpr
    #
    @38
    syl6eleq
    #
    @71
    @0
    cA
    wfn
    #
    @72
    vk
    cA
    @10
    @0
    vf
    vex
    #
    elixp
    simprbi
    syl
    r19.21bi
    snssd
    adantr
    eqssd
    @62
    @8
    @0
    fvex
    ensn1
    syl6eqbr
    ex
    syl5bir
    con3d
    vx
    @64
    neq0
    syl6ib
    @60
    @65
    @58
    vx
    @60
    @65
    @58
    @60
    @65
    wa
    #
    vn
    cA
    @36
    @61
    @2
    @0
    cfv
    #
    cif
    #
    cmpt
    #
    cX
    wcel
    #
    @8
    @80
    @0
    cdif
    #
    cdm
    #
    cuni
    #
    wceq
    #
    @58
    @65
    @60
    @61
    @10
    wcel
    #
    @81
    @61
    @10
    @63
    eldifi
    @60
    @86
    wa
    #
    @80
    @35
    cX
    @87
    @80
    @35
    wcel
    #
    @79
    @4
    wcel
    #
    vn
    cA
    wral
    #
    @87
    @89
    vn
    cA
    @87
    @2
    cA
    wcel
    #
    wa
    #
    @36
    @89
    @92
    @89
    @36
    @86
    @60
    @86
    @91
    simplr
    @36
    @79
    @61
    @4
    @10
    @36
    @61
    @78
    iftrue
    @37
    eleq12d
    syl5ibrcom
    @92
    @89
    @36
    wn
    #
    @78
    @4
    wcel
    #
    @87
    @94
    vn
    cA
    @24
    @94
    vn
    cA
    wral
    #
    @54
    @86
    @24
    @0
    @35
    wcel
    #
    @95
    @24
    @0
    cX
    @35
    @73
    ptcmp.2
    syl6eleq
    #
    @96
    @75
    @95
    vn
    cA
    @4
    @0
    @76
    elixp
    simprbi
    syl
    ad2antrr
    r19.21bi
    @93
    @79
    @78
    @4
    @36
    @61
    @78
    iffalse
    eleq1d
    syl5ibrcom
    pm2.61d
    ralrimiva
    @87
    cA
    cV
    wcel
    #
    @88
    @90
    wb
    wph
    @98
    @1
    @54
    @86
    ptcmp.3
    ad3antrrr
    vn
    cA
    @79
    @4
    cV
    mptelixpg
    syl
    mpbird
    ptcmp.2
    syl6eleqr
    sylan2
    @77
    @8
    @8
    csn
    #
    cuni
    @84
    @8
    vk
    vex
    #
    unisn
    @77
    @99
    @83
    @77
    @99
    vm
    cv
    #
    @80
    cfv
    #
    @101
    @0
    cfv
    #
    wne
    #
    vm
    cA
    crab
    #
    @83
    @77
    vm
    vk
    weq
    #
    vm
    cab
    @101
    cA
    wcel
    #
    @104
    wa
    #
    vm
    cab
    @99
    @105
    @77
    @106
    @108
    vm
    @77
    @106
    @107
    @106
    wa
    @108
    @77
    @106
    @107
    @77
    @107
    @106
    @54
    @24
    @54
    @65
    simplr
    @101
    @8
    cA
    eleq1
    syl5ibrcom
    pm4.71rd
    @77
    @107
    @104
    @106
    @77
    @107
    wa
    #
    @104
    @106
    @61
    @103
    cif
    #
    @103
    wne
    #
    @106
    @107
    @104
    @111
    wb
    @77
    @107
    @102
    @110
    @103
    vn
    @101
    @79
    @110
    cA
    @80
    vn
    vm
    weq
    @36
    @106
    @78
    @103
    @61
    vn
    vm
    vk
    equequ1
    @2
    @101
    @0
    fveq2
    ifbieq2d
    @80
    eqid
    #
    @106
    @61
    @103
    vx
    vex
    #
    @101
    @0
    fvex
    ifex
    fvmpt
    neeq1d
    adantl
    @109
    @111
    @106
    @106
    @110
    @103
    @106
    @61
    @103
    iffalse
    necon1ai
    @109
    @111
    @106
    @61
    @62
    wne
    #
    @65
    @114
    @60
    @107
    @61
    @10
    @62
    eldifsni
    ad2antlr
    @106
    @110
    @61
    @103
    @62
    @106
    @61
    @103
    iftrue
    @101
    @8
    @0
    fveq2
    neeq12d
    syl5ibrcom
    impbid2
    bitrd
    pm5.32da
    bitr4d
    abbidv
    vm
    @8
    df-sn
    @104
    vm
    cA
    df-rab
    3eqtr4g
    @77
    @80
    cA
    wfn
    #
    @75
    @83
    @105
    wceq
    @79
    cvv
    wcel
    #
    vn
    cA
    wral
    @115
    @77
    @116
    vn
    cA
    @36
    @61
    @78
    @113
    @2
    @0
    fvex
    ifex
    rgenw
    vn
    cA
    @79
    @80
    cvv
    @112
    fnmpt
    mp1i
    @24
    @75
    @54
    @65
    @24
    @96
    @75
    @97
    vn
    cA
    @4
    @0
    ixpfn
    syl
    ad2antrr
    vm
    cA
    @80
    @0
    fndmdif
    syl2anc
    eqtr4d
    unieqd
    syl5eqr
    @57
    @85
    vg
    @80
    cX
    @32
    @80
    wceq
    #
    @45
    @84
    @8
    @117
    @44
    @83
    @117
    @43
    @82
    @32
    @80
    @0
    difeq1
    dmeqd
    unieqd
    eqeq2d
    rspcev
    syl2anc
    ex
    exlimdv
    syld
    expimpd
    @6
    @56
    vn
    @8
    cA
    @36
    @5
    @55
    @36
    @4
    @10
    c1o
    cen
    @37
    breq1d
    notbid
    elrab
    @8
    cvv
    wcel
    @59
    @58
    wb
    @100
    vg
    cX
    @45
    @8
    @46
    cvv
    @53
    elrnmpt
    ax-mp
    3imtr4g
    ssrdv
    @47
    @7
    ssnum
    syl2anc
    @25
    @7
    xpnum
    syl2anc
    @24
    @7
    cvv
    wcel
    #
    @11
    cvv
    wcel
    #
    @25
    c0
    wne
    #
    @28
    @24
    @98
    @118
    wph
    @98
    @1
    ptcmp.3
    adantr
    @6
    vn
    cA
    cV
    rabexg
    syl
    #
    @24
    @118
    @10
    cvv
    wcel
    #
    vk
    @7
    wral
    @119
    @121
    @122
    vk
    @7
    @9
    @8
    cF
    fvex
    uniex
    rgenw
    vk
    @7
    @10
    cvv
    cvv
    iunexg
    sylancl
    @24
    @0
    @7
    cres
    #
    @25
    wcel
    #
    @120
    @24
    @41
    @71
    @124
    @42
    @74
    vk
    cA
    @7
    @10
    @0
    resixp
    sylancr
    @25
    @123
    ne0i
    syl
    vk
    @7
    @10
    cvv
    cvv
    ixpiunwdom
    syl3anc
    @26
    @11
    numwdom
    syl2anc
    exlimddv
end
