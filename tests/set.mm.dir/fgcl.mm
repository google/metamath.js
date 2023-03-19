include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "cfg.mm"
include "co.mm"
include "elfg.mm"
include "elfvex.mm"
include "wsbc.mm"
include "wa.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "fbasne0.mm"
include "n0.mm"
include "sylib.mm"
include "fbelss.mm"
include "ex.mm"
include "ancld.mm"
include "eximdv.mm"
include "mpd.mm"
include "df-rex.mm"
include "sylibr.mm"
include "cdm.mm"
include "wb.mm"
include "elfvdm.mm"
include "wceq.mm"
include "sseq2.mm"
include "rexbidv.mm"
include "sbcieg.mm"
include "syl.mm"
include "mpbird.mm"
include "0nelfb.mm"
include "0ex.mm"
include "sbcie.mm"
include "ss0.mm"
include "eleq1d.mm"
include "biimpac.mm"
include "rexlimiva.mm"
include "sylbi.mm"
include "nsyl.mm"
include "w3a.mm"
include "wi.mm"
include "sstr.mm"
include "expcom.mm"
include "reximdv.mm"
include "3ad2ant3.mm"
include "vex.mm"
include "weq.mm"
include "3imtr4g.mm"
include "cin.mm"
include "fbasssin.mm"
include "3expib.mm"
include "sstr2.mm"
include "com12.mm"
include "ss2in.mm"
include "syl11.mm"
include "syl6.mm"
include "exp5c.mm"
include "imp31.mm"
include "impancom.mm"
include "rexlimdv.mm"
include "rexlimdva.mm"
include "impd.mm"
include "3ad2ant1.mm"
include "sseq1.mm"
include "cbvrexv.mm"
include "bitri.mm"
include "anbi12i.mm"
include "inex1.mm"
include "isfild.mm"

theorem fgcl
  let cF: class F
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cY: class Y


  assert |- ( F e. ( fBas ` X ) -> ( X filGen F ) e. ( Fil ` X ) )

  proof
    cF
    cX
    cfbas
    cfv
    wcel
    #
    vy
    cv
    #
    vz
    cv
    #
    wss
    #
    vy
    cF
    wrex
    #
    vz
    vu
    vv
    cX
    cX
    cF
    cfg
    co
    vy
    @2
    cF
    cX
    elfg
    cF
    cX
    cfbas
    elfvex
    @0
    @4
    vz
    cX
    wsbc
    #
    @1
    cX
    wss
    #
    vy
    cF
    wrex
    #
    @0
    @1
    cF
    wcel
    #
    @6
    wa
    #
    vy
    wex
    #
    @7
    @0
    @8
    vy
    wex
    #
    @10
    @0
    cF
    c0
    wne
    @11
    cX
    cF
    fbasne0
    vy
    cF
    n0
    sylib
    @0
    @8
    @9
    vy
    @0
    @8
    @6
    @0
    @8
    @6
    cX
    cF
    @1
    fbelss
    ex
    ancld
    eximdv
    mpd
    @6
    vy
    cF
    df-rex
    sylibr
    @0
    cX
    cfbas
    cdm
    #
    wcel
    @5
    @7
    wb
    cF
    cX
    cfbas
    elfvdm
    @4
    @7
    vz
    cX
    @12
    @2
    cX
    wceq
    @3
    @6
    vy
    cF
    @2
    cX
    @1
    sseq2
    rexbidv
    sbcieg
    syl
    mpbird
    @0
    c0
    cF
    wcel
    #
    @4
    vz
    c0
    wsbc
    #
    cX
    cF
    0nelfb
    @14
    @1
    c0
    wss
    #
    vy
    cF
    wrex
    #
    @13
    @4
    @16
    vz
    c0
    0ex
    @2
    c0
    wceq
    @3
    @15
    vy
    cF
    @2
    c0
    @1
    sseq2
    rexbidv
    sbcie
    @15
    @13
    vy
    cF
    @15
    @8
    @13
    @15
    @1
    c0
    cF
    @1
    ss0
    eleq1d
    biimpac
    rexlimiva
    sylbi
    nsyl
    @0
    vu
    cv
    #
    cX
    wss
    #
    vv
    cv
    #
    @17
    wss
    #
    w3a
    @1
    @19
    wss
    #
    vy
    cF
    wrex
    #
    @1
    @17
    wss
    #
    vy
    cF
    wrex
    #
    @4
    vz
    @19
    wsbc
    #
    @4
    vz
    @17
    wsbc
    #
    @20
    @0
    @22
    @24
    wi
    @18
    @20
    @21
    @23
    vy
    cF
    @21
    @20
    @23
    @1
    @19
    @17
    sstr
    expcom
    reximdv
    3ad2ant3
    @4
    @22
    vz
    @19
    vv
    vex
    vz
    vv
    weq
    @3
    @21
    vy
    cF
    @2
    @19
    @1
    sseq2
    rexbidv
    sbcie
    #
    @4
    @24
    vz
    @17
    vu
    vex
    #
    vz
    vu
    weq
    @3
    @23
    vy
    cF
    @2
    @17
    @1
    sseq2
    rexbidv
    sbcie
    #
    3imtr4g
    @0
    @18
    @19
    cX
    wss
    #
    w3a
    @2
    @17
    wss
    #
    vz
    cF
    wrex
    #
    vw
    cv
    #
    @19
    wss
    #
    vw
    cF
    wrex
    #
    wa
    #
    @1
    @17
    @19
    cin
    #
    wss
    #
    vy
    cF
    wrex
    #
    @26
    @25
    wa
    @4
    vz
    @37
    wsbc
    @0
    @18
    @36
    @39
    wi
    @30
    @0
    @32
    @35
    @39
    @0
    @31
    @35
    @39
    wi
    #
    vz
    cF
    @0
    @2
    cF
    wcel
    #
    wa
    #
    @31
    @40
    @42
    @31
    wa
    @34
    @39
    vw
    cF
    @42
    @33
    cF
    wcel
    #
    @31
    @34
    @39
    wi
    #
    @0
    @41
    @43
    @31
    @44
    wi
    @0
    @41
    @43
    @31
    @34
    @39
    @0
    @41
    @43
    wa
    @1
    @2
    @33
    cin
    #
    wss
    #
    vy
    cF
    wrex
    #
    @31
    @34
    wa
    #
    @39
    wi
    @0
    @41
    @43
    @47
    vy
    @2
    @33
    cF
    cX
    fbasssin
    3expib
    @45
    @37
    wss
    #
    @47
    @39
    @48
    @49
    @46
    @38
    vy
    cF
    @46
    @49
    @38
    @1
    @45
    @37
    sstr2
    com12
    reximdv
    @2
    @17
    @33
    @19
    ss2in
    syl11
    syl6
    exp5c
    imp31
    impancom
    rexlimdv
    ex
    rexlimdva
    impd
    3ad2ant1
    @26
    @32
    @25
    @35
    @26
    @24
    @32
    @29
    @23
    @31
    vy
    vz
    cF
    @1
    @2
    @17
    sseq1
    cbvrexv
    bitri
    @25
    @22
    @35
    @27
    @21
    @34
    vy
    vw
    cF
    @1
    @33
    @19
    sseq1
    cbvrexv
    bitri
    anbi12i
    @4
    @39
    vz
    @37
    @17
    @19
    @28
    inex1
    @2
    @37
    wceq
    @3
    @38
    vy
    cF
    @2
    @37
    @1
    sseq2
    rexbidv
    sbcie
    3imtr4g
    isfild
end
