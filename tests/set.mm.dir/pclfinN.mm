include "cal.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfn.mm"
include "cpw.mm"
include "cin.mm"
include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "cpsubsp.mm"
include "wceq.mm"
include "simpl.mm"
include "cjn.mm"
include "co.mm"
include "cple.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "elin.mm"
include "elpwi.mm"
include "adantl.mm"
include "sylbi.mm"
include "simpll.mm"
include "sstr.mm"
include "ancoms.mm"
include "adantll.mm"
include "eqid.mm"
include "pclclN.mm"
include "syl2anc.mm"
include "psubssat.mm"
include "ex.mm"
include "syl5.mm"
include "ralrimiv.mm"
include "iunss.mm"
include "sylibr.mm"
include "wrex.mm"
include "eliun.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "cbvrexv.mm"
include "bitri.mm"
include "anbi12i.mm"
include "anim2i.mm"
include "w3a.mm"
include "cun.mm"
include "simp2rl.mm"
include "simp12l.mm"
include "unfi.mm"
include "simp2rr.mm"
include "simp12r.mm"
include "unssd.mm"
include "vex.mm"
include "unex.mm"
include "elpw.mm"
include "elind.mm"
include "simp11l.mm"
include "simp11r.mm"
include "sstrd.mm"
include "simp3l.mm"
include "ssun1.mm"
include "a1i.mm"
include "pclssN.mm"
include "syl3anc.mm"
include "simp2l.mm"
include "sseldd.mm"
include "ssun2.mm"
include "simp13.mm"
include "simp3r.mm"
include "psubspi2N.mm"
include "syl33anc.mm"
include "rspcev.mm"
include "3exp.mm"
include "exp5c.mm"
include "rexlimdv.mm"
include "com24.mm"
include "impd.mm"
include "syl5bi.mm"
include "ralrimdv.mm"
include "ralrimivv.mm"
include "wb.mm"
include "ispsubsp.mm"
include "adantr.mm"
include "mpbir2and.mm"
include "csn.mm"
include "snfi.mm"
include "snelpwi.mm"
include "vsnid.mm"
include "ssel2.mm"
include "snatpsubN.mm"
include "pclidN.mm"
include "syl5eleqr.mm"
include "syl6ibr.mm"
include "ssrdv.mm"
include "simpr.mm"
include "simplr.mm"
include "sseld.mm"
include "pclbtwnN.mm"
include "syl22anc.mm"
include "eqcomd.mm"

theorem pclfinN
  let vy: setvar y
  let cA: class A
  let cU: class U
  let cK: class K
  let cX: class X
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vv: setvar v
  let vw: setvar w
  assume pclfin.a: |- A = ( Atoms ` K )
  assume pclfin.c: |- U = ( PCl ` K )

  disjoint A y
  disjoint U y
  disjoint K y
  disjoint X y
  disjoint p q
  disjoint p r
  disjoint p v
  disjoint p w
  disjoint p y
  disjoint A p
  disjoint q r
  disjoint q v
  disjoint q w
  disjoint q y
  disjoint A q
  disjoint r v
  disjoint r w
  disjoint r y
  disjoint A r
  disjoint v w
  disjoint v y
  disjoint A v
  disjoint w y
  disjoint A w
  disjoint U p
  disjoint U q
  disjoint U r
  disjoint U v
  disjoint U w
  disjoint K p
  disjoint K q
  disjoint K r
  disjoint K v
  disjoint K w
  disjoint X p
  disjoint X q
  disjoint X r
  disjoint X v
  disjoint X w
  assert |- ( ( K e. AtLat /\ X C_ A ) -> ( U ` X ) = U_ y e. ( Fin i^i ~P X ) ( U ` y ) )

  proof
    cK
    cal
    wcel
    #
    cX
    cA
    wss
    #
    wa
    #
    vy
    cfn
    cX
    cpw
    #
    cin
    #
    vy
    cv
    #
    cU
    cfv
    #
    ciun
    #
    cX
    cU
    cfv
    #
    @2
    @0
    @7
    cK
    cpsubsp
    cfv
    #
    wcel
    #
    cX
    @7
    wss
    @7
    @8
    wss
    @7
    @8
    wceq
    @0
    @1
    simpl
    @2
    @10
    @7
    cA
    wss
    #
    vr
    cv
    #
    vp
    cv
    #
    vq
    cv
    #
    cK
    cjn
    cfv
    #
    co
    cK
    cple
    cfv
    #
    wbr
    #
    @12
    @7
    wcel
    #
    wi
    #
    vr
    cA
    wral
    #
    vq
    @7
    wral
    vp
    @7
    wral
    #
    @2
    @6
    cA
    wss
    #
    vy
    @4
    wral
    @11
    @2
    @22
    vy
    @4
    @5
    @4
    wcel
    #
    @5
    cX
    wss
    #
    @2
    @22
    @23
    @5
    cfn
    wcel
    #
    @5
    @3
    wcel
    #
    wa
    @24
    @5
    cfn
    @3
    elin
    @26
    @24
    @25
    @5
    cX
    elpwi
    adantl
    sylbi
    #
    @2
    @24
    @22
    @2
    @24
    wa
    #
    @0
    @6
    @9
    wcel
    #
    @22
    @0
    @1
    @24
    simpll
    #
    @28
    @0
    @5
    cA
    wss
    #
    @29
    @30
    @1
    @24
    @31
    @0
    @24
    @1
    @31
    @5
    cX
    cA
    sstr
    ancoms
    adantll
    cA
    @9
    cU
    cK
    cal
    @5
    pclfin.a
    @9
    eqid
    #
    pclfin.c
    pclclN
    syl2anc
    cA
    cal
    @9
    cK
    @6
    pclfin.a
    @32
    psubssat
    syl2anc
    ex
    syl5
    ralrimiv
    vy
    @4
    @6
    cA
    iunss
    sylibr
    @2
    @20
    vp
    vq
    @7
    @7
    @2
    @13
    @7
    wcel
    #
    @14
    @7
    wcel
    #
    wa
    #
    @19
    vr
    cA
    @35
    @13
    vw
    cv
    #
    cU
    cfv
    #
    wcel
    #
    vw
    @4
    wrex
    #
    @14
    vv
    cv
    #
    cU
    cfv
    #
    wcel
    #
    vv
    @4
    wrex
    #
    wa
    @2
    @12
    cA
    wcel
    #
    @19
    wi
    #
    @33
    @39
    @34
    @43
    @33
    @13
    @6
    wcel
    #
    vy
    @4
    wrex
    @39
    vy
    @13
    @4
    @6
    eliun
    @46
    @38
    vy
    vw
    @4
    @5
    @36
    wceq
    @6
    @37
    @13
    @5
    @36
    cU
    fveq2
    eleq2d
    cbvrexv
    bitri
    @34
    @14
    @6
    wcel
    #
    vy
    @4
    wrex
    @43
    vy
    @14
    @4
    @6
    eliun
    @47
    @42
    vy
    vv
    @4
    @5
    @40
    wceq
    @6
    @41
    @14
    @5
    @40
    cU
    fveq2
    eleq2d
    cbvrexv
    bitri
    anbi12i
    @2
    @39
    @43
    @45
    @2
    @38
    @43
    @45
    wi
    #
    vw
    @4
    @36
    @4
    wcel
    #
    @36
    cfn
    wcel
    #
    @36
    cX
    wss
    #
    wa
    #
    @2
    @38
    @48
    wi
    @49
    @50
    @36
    @3
    wcel
    #
    wa
    @52
    @36
    cfn
    @3
    elin
    @53
    @51
    @50
    @36
    cX
    elpwi
    anim2i
    sylbi
    @2
    @43
    @38
    @52
    @45
    @2
    @42
    @38
    @52
    @45
    wi
    wi
    #
    vv
    @4
    @40
    @4
    wcel
    #
    @40
    cfn
    wcel
    #
    @40
    cX
    wss
    #
    wa
    #
    @2
    @42
    @54
    wi
    @55
    @56
    @40
    @3
    wcel
    #
    wa
    @58
    @40
    cfn
    @3
    elin
    @59
    @57
    @56
    @40
    cX
    elpwi
    anim2i
    sylbi
    @2
    @58
    @42
    @54
    @2
    @58
    @42
    w3a
    #
    @38
    @52
    @44
    @17
    @18
    @60
    @38
    @52
    wa
    #
    @44
    @17
    wa
    #
    @18
    @60
    @61
    @62
    w3a
    #
    @12
    @6
    wcel
    #
    vy
    @4
    wrex
    #
    @18
    @63
    @36
    @40
    cun
    #
    @4
    wcel
    @12
    @66
    cU
    cfv
    #
    wcel
    #
    @65
    @63
    cfn
    @3
    @66
    @63
    @50
    @56
    @66
    cfn
    wcel
    @50
    @51
    @38
    @60
    @62
    simp2rl
    @56
    @57
    @2
    @42
    @61
    @62
    simp12l
    @36
    @40
    unfi
    syl2anc
    @63
    @66
    cX
    wss
    @66
    @3
    wcel
    @63
    @36
    @40
    cX
    @50
    @51
    @38
    @60
    @62
    simp2rr
    #
    @56
    @57
    @2
    @42
    @61
    @62
    simp12r
    #
    unssd
    @66
    cX
    @36
    @40
    vw
    vex
    vv
    vex
    unex
    elpw
    sylibr
    elind
    @63
    @0
    @67
    @9
    wcel
    #
    @44
    @13
    @67
    wcel
    @14
    @67
    wcel
    @17
    @68
    @0
    @1
    @58
    @42
    @61
    @62
    simp11l
    #
    @63
    @0
    @66
    cA
    wss
    #
    @71
    @72
    @63
    @36
    @40
    cA
    @63
    @36
    cX
    cA
    @69
    @0
    @1
    @58
    @42
    @61
    @62
    simp11r
    #
    sstrd
    @63
    @40
    cX
    cA
    @70
    @74
    sstrd
    unssd
    #
    cA
    @9
    cU
    cK
    cal
    @66
    pclfin.a
    @32
    pclfin.c
    pclclN
    syl2anc
    @60
    @61
    @44
    @17
    simp3l
    @63
    @37
    @67
    @13
    @63
    @0
    @36
    @66
    wss
    #
    @73
    @37
    @67
    wss
    @72
    @76
    @63
    @36
    @40
    ssun1
    a1i
    @75
    cA
    cU
    cK
    cal
    @36
    @66
    pclfin.a
    pclfin.c
    pclssN
    syl3anc
    @60
    @38
    @52
    @62
    simp2l
    sseldd
    @63
    @41
    @67
    @14
    @63
    @0
    @40
    @66
    wss
    #
    @73
    @41
    @67
    wss
    @72
    @77
    @63
    @40
    @36
    ssun2
    a1i
    @75
    cA
    cU
    cK
    cal
    @40
    @66
    pclfin.a
    pclfin.c
    pclssN
    syl3anc
    @2
    @58
    @42
    @61
    @62
    simp13
    sseldd
    @60
    @61
    @44
    @17
    simp3r
    cA
    cal
    @12
    @13
    @14
    @9
    @15
    cK
    @16
    @67
    @16
    eqid
    #
    @15
    eqid
    #
    pclfin.a
    @32
    psubspi2N
    syl33anc
    @64
    @68
    vy
    @66
    @4
    @5
    @66
    wceq
    @6
    @67
    @12
    @5
    @66
    cU
    fveq2
    eleq2d
    rspcev
    syl2anc
    vy
    @12
    @4
    @6
    eliun
    sylibr
    3exp
    exp5c
    3exp
    syl5
    rexlimdv
    com24
    syl5
    rexlimdv
    impd
    syl5bi
    ralrimdv
    ralrimivv
    @0
    @10
    @11
    @21
    wa
    wb
    @1
    cA
    cal
    @9
    @15
    cK
    @16
    @7
    vr
    vq
    vp
    @78
    @79
    pclfin.a
    @32
    ispsubsp
    adantr
    mpbir2and
    @2
    vw
    cX
    @7
    @2
    @36
    cX
    wcel
    #
    @36
    @6
    wcel
    #
    vy
    @4
    wrex
    #
    @36
    @7
    wcel
    #
    @2
    @80
    @82
    @2
    @80
    wa
    #
    @36
    csn
    #
    @4
    wcel
    @36
    @85
    cU
    cfv
    #
    wcel
    #
    @82
    @84
    cfn
    @3
    @85
    @85
    cfn
    wcel
    @84
    @36
    snfi
    a1i
    @80
    @85
    @3
    wcel
    @2
    @36
    cX
    snelpwi
    adantl
    elind
    @84
    @36
    @85
    @86
    vw
    vsnid
    @84
    @0
    @85
    @9
    wcel
    #
    @86
    @85
    wceq
    @0
    @1
    @80
    simpll
    #
    @84
    @0
    @36
    cA
    wcel
    #
    @88
    @89
    @1
    @80
    @90
    @0
    cX
    cA
    @36
    ssel2
    adantll
    cA
    @36
    @9
    cK
    pclfin.a
    @32
    snatpsubN
    syl2anc
    @9
    cU
    cK
    cal
    @85
    @32
    pclfin.c
    pclidN
    syl2anc
    syl5eleqr
    @81
    @87
    vy
    @85
    @4
    @5
    @85
    wceq
    @6
    @86
    @36
    @5
    @85
    cU
    fveq2
    eleq2d
    rspcev
    syl2anc
    ex
    vy
    @36
    @4
    @6
    eliun
    #
    syl6ibr
    ssrdv
    @2
    vw
    @7
    @8
    @83
    @82
    @2
    @36
    @8
    wcel
    #
    @91
    @2
    @81
    @92
    vy
    @4
    @23
    @24
    @2
    @81
    @92
    wi
    #
    @27
    @2
    @24
    @93
    @28
    @6
    @8
    @36
    @28
    @0
    @24
    @1
    @6
    @8
    wss
    @30
    @2
    @24
    simpr
    @0
    @1
    @24
    simplr
    cA
    cU
    cK
    cal
    @5
    cX
    pclfin.a
    pclfin.c
    pclssN
    syl3anc
    sseld
    ex
    syl5
    rexlimdv
    syl5bi
    ssrdv
    @9
    cU
    cK
    cal
    @7
    cX
    @32
    pclfin.c
    pclbtwnN
    syl22anc
    eqcomd
end
