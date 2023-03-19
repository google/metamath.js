include "cmrc.mm"
include "cmre.mm"
include "cfv.mm"
include "cima.mm"
include "wcel.mm"
include "cvv.mm"
include "cpw.mm"
include "wf.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "wceq.mm"
include "w3a.mm"
include "wi.mm"
include "wal.mm"
include "wrex.mm"
include "wfun.mm"
include "crn.mm"
include "cuni.mm"
include "wfn.mm"
include "fnmrc.mm"
include "fnfun.mm"
include "ax-mp.mm"
include "fvelima.mm"
include "mpan.mm"
include "elfvex.mm"
include "eqid.mm"
include "mrcf.mm"
include "mresspw.mm"
include "fssd.mm"
include "mrcssid.mm"
include "adantrr.mm"
include "mrcss.mm"
include "3expb.mm"
include "ancom2s.mm"
include "mrcidm.mm"
include "3jca.mm"
include "ex.mm"
include "alrimivv.mm"
include "feq1.mm"
include "fveq1.mm"
include "sseq2d.mm"
include "sseq12d.mm"
include "id.mm"
include "fveq12d.mm"
include "eqeq12d.mm"
include "3anbi123d.mm"
include "imbi2d.mm"
include "2albidv.mm"
include "3anbi23d.mm"
include "syl5ibcom.mm"
include "rexlimiv.mm"
include "syl.mm"
include "cid.mm"
include "cin.mm"
include "cdm.mm"
include "simp1.mm"
include "simp2.mm"
include "ssid.mm"
include "3simpb.mm"
include "imim2i.mm"
include "2alimi.mm"
include "vex.mm"
include "weq.mm"
include "wb.mm"
include "sseq1.mm"
include "adantr.mm"
include "sseq12.mm"
include "ancoms.mm"
include "anbi12d.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "imbi12d.mm"
include "spc2gv.mm"
include "mp2an.mm"
include "3ad2ant3.mm"
include "mpan2i.mm"
include "imp.mm"
include "simpld.mm"
include "syl2anr.mm"
include "3impib.mm"
include "simprd.mm"
include "ismrcd2.mm"
include "ismrcd1.mm"
include "fvssunirn.mm"
include "fndm.mm"
include "sseqtr4i.mm"
include "funfvima2.mm"
include "eqeltrd.mm"
include "impbii.mm"

theorem ismrc
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cF: class F
  let vz: setvar z
  let vw: setvar w

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F z
  disjoint F w
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint B z
  disjoint B w
  assert |- ( F e. ( mrCls " ( Moore ` B ) ) <-> ( B e. _V /\ F : ~P B --> ~P B /\ A. x A. y ( ( x C_ B /\ y C_ x ) -> ( x C_ ( F ` x ) /\ ( F ` y ) C_ ( F ` x ) /\ ( F ` ( F ` x ) ) = ( F ` x ) ) ) ) )

  proof
    cF
    cmrc
    cB
    cmre
    cfv
    #
    cima
    #
    wcel
    #
    cB
    cvv
    wcel
    #
    cB
    cpw
    #
    @4
    cF
    wf
    #
    vx
    cv
    #
    cB
    wss
    #
    vy
    cv
    #
    @6
    wss
    #
    wa
    #
    @6
    @6
    cF
    cfv
    #
    wss
    #
    @8
    cF
    cfv
    #
    @11
    wss
    #
    @11
    cF
    cfv
    #
    @11
    wceq
    #
    w3a
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
    w3a
    #
    @2
    vz
    cv
    #
    cmrc
    cfv
    #
    cF
    wceq
    #
    vz
    @0
    wrex
    #
    @20
    cmrc
    wfun
    #
    @2
    @24
    cmrc
    cmre
    crn
    cuni
    #
    wfn
    #
    @25
    fnmrc
    @26
    cmrc
    fnfun
    ax-mp
    #
    vz
    cF
    @0
    cmrc
    fvelima
    mpan
    @23
    @20
    vz
    @0
    @21
    @0
    wcel
    #
    @3
    @4
    @4
    @22
    wf
    #
    @10
    @6
    @6
    @22
    cfv
    #
    wss
    #
    @8
    @22
    cfv
    #
    @31
    wss
    #
    @31
    @22
    cfv
    #
    @31
    wceq
    #
    w3a
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
    w3a
    @23
    @20
    @29
    @3
    @30
    @39
    @21
    cB
    cmre
    elfvex
    @29
    @4
    @21
    @4
    @22
    @21
    @22
    cB
    @22
    eqid
    #
    mrcf
    @21
    cB
    mresspw
    fssd
    @29
    @38
    vx
    vy
    @29
    @10
    @37
    @29
    @10
    wa
    @32
    @34
    @36
    @29
    @7
    @32
    @9
    @21
    @6
    @22
    cB
    @40
    mrcssid
    adantrr
    @29
    @9
    @7
    @34
    @29
    @9
    @7
    @34
    @21
    @8
    @22
    @6
    cB
    @40
    mrcss
    3expb
    ancom2s
    @29
    @7
    @36
    @9
    @21
    @6
    @22
    cB
    @40
    mrcidm
    adantrr
    3jca
    ex
    alrimivv
    3jca
    @23
    @30
    @5
    @39
    @19
    @3
    @4
    @4
    @22
    cF
    feq1
    @23
    @38
    @18
    vx
    vy
    @23
    @37
    @17
    @10
    @23
    @32
    @12
    @34
    @14
    @36
    @16
    @23
    @31
    @11
    @6
    @6
    @22
    cF
    fveq1
    #
    sseq2d
    @23
    @33
    @13
    @31
    @11
    @8
    @22
    cF
    fveq1
    @41
    sseq12d
    @23
    @35
    @15
    @31
    @11
    @23
    @31
    @11
    @22
    cF
    @23
    id
    @41
    fveq12d
    @41
    eqeq12d
    3anbi123d
    imbi2d
    2albidv
    3anbi23d
    syl5ibcom
    rexlimiv
    syl
    @20
    cF
    cF
    cid
    cin
    cdm
    #
    cmrc
    cfv
    #
    @1
    @20
    vz
    vw
    cB
    cF
    cvv
    @3
    @5
    @19
    simp1
    #
    @3
    @5
    @19
    simp2
    #
    @20
    @21
    cB
    wss
    #
    wa
    #
    @21
    @21
    cF
    cfv
    #
    wss
    #
    @48
    cF
    cfv
    #
    @48
    wceq
    #
    @20
    @46
    @49
    @51
    wa
    #
    @20
    @46
    @21
    @21
    wss
    #
    @52
    @21
    ssid
    @19
    @3
    @46
    @53
    wa
    #
    @52
    wi
    #
    @5
    @19
    @10
    @12
    @16
    wa
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
    @55
    @18
    @57
    vx
    vy
    @17
    @56
    @10
    @12
    @14
    @16
    3simpb
    imim2i
    2alimi
    @21
    cvv
    wcel
    #
    @59
    @58
    @55
    wi
    vz
    vex
    #
    @60
    @57
    @55
    vx
    vy
    @21
    @21
    cvv
    cvv
    vx
    vz
    weq
    #
    vy
    vz
    weq
    #
    wa
    #
    @10
    @54
    @56
    @52
    @63
    @7
    @46
    @9
    @53
    @61
    @7
    @46
    wb
    #
    @62
    @6
    @21
    cB
    sseq1
    #
    adantr
    @62
    @61
    @9
    @53
    wb
    @8
    @21
    @6
    @21
    sseq12
    ancoms
    anbi12d
    @63
    @12
    @49
    @16
    @51
    @61
    @12
    @49
    wb
    @62
    @61
    @6
    @21
    @11
    @48
    @61
    id
    @6
    @21
    cF
    fveq2
    #
    sseq12d
    adantr
    @61
    @16
    @51
    wb
    @62
    @61
    @15
    @50
    @11
    @48
    @61
    @11
    @48
    cF
    @66
    fveq2d
    @66
    eqeq12d
    adantr
    anbi12d
    imbi12d
    spc2gv
    mp2an
    syl
    3ad2ant3
    mpan2i
    imp
    #
    simpld
    #
    @20
    @46
    vw
    cv
    #
    @21
    wss
    #
    @69
    cF
    cfv
    #
    @48
    wss
    #
    @20
    @10
    @14
    wi
    #
    vy
    wal
    vx
    wal
    #
    @46
    @70
    wa
    #
    @72
    wi
    #
    @19
    @3
    @74
    @5
    @18
    @73
    vx
    vy
    @17
    @14
    @10
    @12
    @14
    @16
    simp2
    imim2i
    2alimi
    3ad2ant3
    @59
    @69
    cvv
    wcel
    @74
    @76
    wi
    @60
    vw
    vex
    @73
    @76
    vx
    vy
    @21
    @69
    cvv
    cvv
    @61
    vy
    vw
    weq
    #
    wa
    #
    @10
    @75
    @14
    @72
    @78
    @7
    @46
    @9
    @70
    @61
    @64
    @77
    @65
    adantr
    @77
    @61
    @9
    @70
    wb
    @8
    @69
    @6
    @21
    sseq12
    ancoms
    anbi12d
    @77
    @13
    @71
    wceq
    @11
    @48
    wceq
    @14
    @72
    wb
    @61
    @8
    @69
    cF
    fveq2
    @66
    @13
    @71
    @11
    @48
    sseq12
    syl2anr
    imbi12d
    spc2gv
    mp2an
    syl
    3impib
    #
    @47
    @49
    @51
    @67
    simprd
    #
    ismrcd2
    @20
    @42
    @0
    wcel
    #
    @43
    @1
    wcel
    #
    @20
    vz
    vw
    cB
    cF
    cvv
    @44
    @45
    @68
    @79
    @80
    ismrcd1
    @25
    @0
    cmrc
    cdm
    #
    wss
    @81
    @82
    wi
    @28
    @0
    @26
    @83
    cmre
    cB
    fvssunirn
    @27
    @83
    @26
    wceq
    fnmrc
    @26
    cmrc
    fndm
    ax-mp
    sseqtr4i
    @0
    @42
    cmrc
    funfvima2
    mp2an
    syl
    eqeltrd
    impbii
end
