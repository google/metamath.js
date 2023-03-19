include "wceq.mm"
include "cfne.mm"
include "wbr.mm"
include "cv.mm"
include "wss.mm"
include "cref.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "crab.mm"
include "cvv.mm"
include "wcel.mm"
include "fnerel.mm"
include "brrelex2i.mm"
include "adantl.mm"
include "rabexg.mm"
include "syl.mm"
include "ssrab2.mm"
include "a1i.mm"
include "cuni.mm"
include "wral.mm"
include "eleq2i.mm"
include "eluni.mm"
include "bitri.mm"
include "wi.mm"
include "fnessex.mm"
include "3expia.mm"
include "adantll.mm"
include "sseq2.mm"
include "rspcev.mm"
include "ex.mm"
include "anim2d.mm"
include "reximdv.mm"
include "syld.mm"
include "com23.mm"
include "impd.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "elunirab.mm"
include "syl6ibr.mm"
include "ssrdv.mm"
include "unissi.mm"
include "simpl.mm"
include "syl6req.mm"
include "syl5sseq.mm"
include "eqssd.mm"
include "3expb.mm"
include "expcom.mm"
include "ad2antll.mm"
include "com12.mm"
include "ad2antrl.mm"
include "jcad.mm"
include "sseq1.mm"
include "rexbidv.mm"
include "elrab.mm"
include "simpr.mm"
include "reximdv2.mm"
include "mpd.mm"
include "ralrimivva.mm"
include "wb.mm"
include "eqid.mm"
include "isfne2.mm"
include "3syl.mm"
include "mpbir2and.mm"
include "cbvrexv.mm"
include "biimpi.mm"
include "ralrimiv.mm"
include "isref.mm"
include "jca32.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "sylc.mm"
include "simprrl.mm"
include "fnebas.mm"
include "eqtr3d.mm"
include "syl6eq.mm"
include "vuniex.mm"
include "syl6eqelr.mm"
include "uniexb.mm"
include "sylibr.mm"
include "simprl.mm"
include "fness.mm"
include "syl3anc.mm"
include "fnetr.mm"
include "syl2anc.mm"
include "impbid.mm"

theorem fnessref
  let cA: class A
  let cB: class B
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume fnessref.1: |- X = U. A
  assume fnessref.2: |- Y = U. B

  disjoint A c
  disjoint B c
  disjoint X c
  disjoint Y c
  disjoint c t
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B t
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint X t
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y t
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  assert |- ( X = Y -> ( A Fne B <-> E. c ( c C_ B /\ ( A Fne c /\ c Ref A ) ) ) )

  proof
    cX
    cY
    wceq
    #
    cA
    cB
    cfne
    wbr
    #
    vc
    cv
    #
    cB
    wss
    #
    cA
    @2
    cfne
    wbr
    #
    @2
    cA
    cref
    wbr
    #
    wa
    #
    wa
    #
    vc
    wex
    #
    @0
    @1
    @8
    @0
    @1
    wa
    #
    vx
    cv
    #
    vy
    cv
    #
    wss
    #
    vy
    cA
    wrex
    #
    vx
    cB
    crab
    #
    cvv
    wcel
    #
    @14
    cB
    wss
    #
    cA
    @14
    cfne
    wbr
    #
    @14
    cA
    cref
    wbr
    #
    wa
    #
    wa
    #
    @8
    @9
    cB
    cvv
    wcel
    #
    @15
    @1
    @21
    @0
    cA
    cB
    cfne
    fnerel
    brrelex2i
    adantl
    #
    @13
    vx
    cB
    cvv
    rabexg
    #
    syl
    @9
    @16
    @17
    @18
    @16
    @9
    @13
    vx
    cB
    ssrab2
    #
    a1i
    @9
    @17
    cX
    @14
    cuni
    #
    wceq
    #
    vt
    cv
    #
    vw
    cv
    #
    wcel
    #
    @28
    vz
    cv
    #
    wss
    #
    wa
    #
    vw
    @14
    wrex
    #
    vt
    @30
    wral
    vz
    cA
    wral
    #
    @9
    cX
    @25
    @9
    vt
    cX
    @25
    @9
    @27
    cX
    wcel
    #
    @27
    @10
    wcel
    #
    @13
    wa
    #
    vx
    cB
    wrex
    #
    @27
    @25
    wcel
    @35
    @27
    @30
    wcel
    #
    @30
    cA
    wcel
    #
    wa
    #
    vz
    wex
    #
    @9
    @38
    @35
    @27
    cA
    cuni
    #
    wcel
    @42
    cX
    @43
    @27
    fnessref.1
    eleq2i
    vz
    @27
    cA
    eluni
    bitri
    @9
    @41
    @38
    vz
    @9
    @39
    @40
    @38
    @9
    @40
    @39
    @38
    @9
    @40
    @39
    @38
    wi
    @9
    @40
    wa
    #
    @39
    @36
    @10
    @30
    wss
    #
    wa
    #
    vx
    cB
    wrex
    #
    @38
    @1
    @40
    @39
    @47
    wi
    @0
    @1
    @40
    @39
    @47
    vx
    cA
    cB
    @27
    @30
    fnessex
    3expia
    adantll
    @44
    @46
    @37
    vx
    cB
    @44
    @45
    @13
    @36
    @40
    @45
    @13
    wi
    @9
    @40
    @45
    @13
    @12
    @45
    vy
    @30
    cA
    @11
    @30
    @10
    sseq2
    rspcev
    ex
    adantl
    anim2d
    reximdv
    syld
    ex
    com23
    impd
    exlimdv
    syl5bi
    @13
    vx
    @27
    cB
    elunirab
    syl6ibr
    ssrdv
    @9
    cB
    cuni
    #
    @25
    cX
    @14
    cB
    @24
    unissi
    @9
    cX
    cY
    @48
    @0
    @1
    simpl
    fnessref.2
    syl6req
    syl5sseq
    eqssd
    #
    @9
    @33
    vz
    vt
    cA
    @30
    @9
    @40
    @39
    wa
    #
    wa
    #
    @32
    vw
    cB
    wrex
    #
    @33
    @1
    @50
    @52
    @0
    @1
    @40
    @39
    @52
    vw
    cA
    cB
    @27
    @30
    fnessex
    3expb
    adantll
    @51
    @32
    @32
    vw
    cB
    @14
    @51
    @28
    cB
    wcel
    #
    @32
    wa
    #
    @28
    @14
    wcel
    #
    @32
    @51
    @54
    @53
    @28
    @11
    wss
    #
    vy
    cA
    wrex
    #
    wa
    @55
    @51
    @54
    @53
    @57
    @54
    @53
    wi
    @51
    @53
    @32
    simpl
    a1i
    @40
    @54
    @57
    wi
    @9
    @39
    @54
    @40
    @57
    @31
    @40
    @57
    wi
    @53
    @29
    @40
    @31
    @57
    @56
    @31
    vy
    @30
    cA
    @11
    @30
    @28
    sseq2
    rspcev
    expcom
    ad2antll
    com12
    ad2antrl
    jcad
    @13
    @57
    vx
    @28
    cB
    @10
    @28
    wceq
    @12
    @56
    vy
    cA
    @10
    @28
    @11
    sseq1
    rexbidv
    elrab
    syl6ibr
    @54
    @32
    wi
    @51
    @53
    @32
    simpr
    a1i
    jcad
    reximdv2
    mpd
    ralrimivva
    @9
    @21
    @15
    @17
    @26
    @34
    wa
    wb
    @22
    @23
    vz
    vt
    vw
    cA
    @14
    cvv
    cX
    @25
    fnessref.1
    @25
    eqid
    #
    isfne2
    3syl
    mpbir2and
    @9
    @18
    @26
    @30
    @28
    wss
    #
    vw
    cA
    wrex
    #
    vz
    @14
    wral
    #
    @49
    @9
    @60
    vz
    @14
    @30
    @14
    wcel
    @30
    cB
    wcel
    #
    @30
    @11
    wss
    #
    vy
    cA
    wrex
    #
    wa
    #
    @9
    @60
    @13
    @64
    vx
    @30
    cB
    @10
    @30
    wceq
    @12
    @63
    vy
    cA
    @10
    @30
    @11
    sseq1
    rexbidv
    elrab
    @65
    @60
    wi
    @9
    @64
    @60
    @62
    @64
    @60
    @63
    @59
    vy
    vw
    cA
    @11
    @28
    @30
    sseq2
    cbvrexv
    biimpi
    adantl
    a1i
    syl5bi
    ralrimiv
    @9
    @21
    @15
    @18
    @26
    @61
    wa
    wb
    @22
    @23
    vz
    vw
    @14
    cA
    cvv
    @25
    cX
    @58
    fnessref.1
    isref
    3syl
    mpbir2and
    jca32
    @7
    @20
    vc
    @14
    cvv
    @2
    @14
    wceq
    #
    @3
    @16
    @6
    @19
    @2
    @14
    cB
    sseq1
    @66
    @4
    @17
    @5
    @18
    @2
    @14
    cA
    cfne
    breq2
    @2
    @14
    cA
    cref
    breq1
    anbi12d
    anbi12d
    spcegv
    sylc
    ex
    @0
    @7
    @1
    vc
    @0
    @7
    @1
    @0
    @7
    wa
    #
    @4
    @2
    cB
    cfne
    wbr
    #
    @1
    @0
    @3
    @4
    @5
    simprrl
    #
    @67
    @21
    @3
    @2
    cuni
    #
    cY
    wceq
    @68
    @67
    @48
    cvv
    wcel
    @21
    @67
    @48
    @70
    cvv
    @67
    @70
    cY
    @48
    @67
    cX
    @70
    cY
    @67
    @4
    cX
    @70
    wceq
    @69
    cA
    @2
    cX
    @70
    fnessref.1
    @70
    eqid
    #
    fnebas
    syl
    @0
    @7
    simpl
    eqtr3d
    #
    fnessref.2
    syl6eq
    vc
    vuniex
    syl6eqelr
    cB
    uniexb
    sylibr
    @0
    @3
    @6
    simprl
    @72
    @2
    cB
    cvv
    @70
    cY
    @71
    fnessref.2
    fness
    syl3anc
    cA
    @2
    cB
    fnetr
    syl2anc
    ex
    exlimdv
    impbid
end
