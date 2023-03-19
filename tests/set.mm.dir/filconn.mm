include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "cuni.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "cconn.mm"
include "id.mm"
include "filunibas.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "ctop.mm"
include "ccld.mm"
include "cin.mm"
include "cpr.mm"
include "wss.mm"
include "cv.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "wa.mm"
include "wn.mm"
include "wex.mm"
include "nss.mm"
include "simpll.mm"
include "wo.mm"
include "ssel2.mm"
include "adantll.mm"
include "elun.mm"
include "sylib.mm"
include "orcomd.mm"
include "ord.mm"
include "impr.mm"
include "uniss.mm"
include "ad2antlr.mm"
include "uniun.mm"
include "0ex.mm"
include "unisn.mm"
include "uneq2i.mm"
include "un0.mm"
include "3eqtrri.mm"
include "syl6sseqr.mm"
include "elssuni.mm"
include "ad2antrl.mm"
include "filss.mm"
include "syl13anc.mm"
include "elun1.mm"
include "syl.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "wceq.mm"
include "uni0b.mm"
include "ssun2.mm"
include "snid.mm"
include "sselii.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "sylbir.mm"
include "pm2.61d2.mm"
include "alrimiv.mm"
include "w3a.mm"
include "filin.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "elsni.mm"
include "ineq2.mm"
include "in0.mm"
include "syl6eq.mm"
include "syl6eqel.mm"
include "rgen.mm"
include "ralun.mm"
include "sylancl.mm"
include "ineq1.mm"
include "0in.mm"
include "ralrimivw.mm"
include "cvv.mm"
include "wb.mm"
include "p0ex.mm"
include "unexg.mm"
include "mpan2.mm"
include "istopg.mm"
include "mpbir2and.mm"
include "cdif.mm"
include "cldopn.mm"
include "cfbas.mm"
include "filfbas.mm"
include "fbncp.mm"
include "sylan.mm"
include "pm2.21d.mm"
include "a1i13.mm"
include "jaod.mm"
include "imp.mm"
include "adantl.mm"
include "ssdif0.mm"
include "biimpri.mm"
include "eqss.mm"
include "simplbi2.mm"
include "syl2im.mm"
include "syl5.mm"
include "orim12d.mm"
include "expimpd.mm"
include "elin.mm"
include "vex.mm"
include "elpr.mm"
include "3imtr4g.mm"
include "ssrdv.mm"
include "isconn2.mm"
include "sylanbrc.mm"

theorem filconn
  let cF: class F
  let cX: class X
  let vx: setvar x
  let vy: setvar y


  assert |- ( F e. ( Fil ` X ) -> ( F u. { (/) } ) e. Conn )

  proof
    cF
    cX
    cfil
    cfv
    #
    wcel
    #
    cF
    cF
    cuni
    #
    cfil
    cfv
    #
    wcel
    #
    cF
    c0
    csn
    #
    cun
    #
    cconn
    wcel
    #
    @1
    cF
    @0
    @3
    @1
    id
    @1
    @2
    cX
    cfil
    cF
    cX
    filunibas
    fveq2d
    eleqtrrd
    @4
    @6
    ctop
    wcel
    #
    @6
    @6
    ccld
    cfv
    #
    cin
    #
    c0
    @2
    cpr
    #
    wss
    @7
    @4
    @8
    vx
    cv
    #
    @6
    wss
    #
    @12
    cuni
    #
    @6
    wcel
    #
    wi
    #
    vx
    wal
    #
    @12
    vy
    cv
    #
    cin
    #
    @6
    wcel
    #
    vy
    @6
    wral
    #
    vx
    @6
    wral
    #
    @4
    @16
    vx
    @4
    @13
    @15
    @4
    @13
    wa
    #
    @12
    @5
    wss
    #
    @15
    @24
    wn
    @18
    @12
    wcel
    #
    @18
    @5
    wcel
    #
    wn
    #
    wa
    #
    vy
    wex
    @23
    @15
    vy
    @12
    @5
    nss
    @23
    @28
    @15
    vy
    @23
    @28
    @15
    @23
    @28
    wa
    #
    @14
    cF
    wcel
    #
    @15
    @29
    @4
    @18
    cF
    wcel
    #
    @14
    @2
    wss
    @18
    @14
    wss
    #
    @30
    @4
    @13
    @28
    simpll
    @23
    @25
    @27
    @31
    @23
    @25
    wa
    #
    @26
    @31
    @33
    @31
    @26
    @33
    @18
    @6
    wcel
    #
    @31
    @26
    wo
    @13
    @25
    @34
    @4
    @12
    @6
    @18
    ssel2
    adantll
    @18
    cF
    @5
    elun
    sylib
    orcomd
    ord
    impr
    @29
    @14
    @6
    cuni
    #
    @2
    @13
    @14
    @35
    wss
    @4
    @28
    @12
    @6
    uniss
    ad2antlr
    @35
    @2
    @5
    cuni
    #
    cun
    @2
    c0
    cun
    @2
    cF
    @5
    uniun
    @36
    c0
    @2
    c0
    0ex
    unisn
    uneq2i
    @2
    un0
    3eqtrri
    #
    syl6sseqr
    @25
    @32
    @23
    @27
    @18
    @12
    elssuni
    ad2antrl
    @18
    @14
    cF
    @2
    filss
    syl13anc
    @14
    cF
    @5
    elun1
    syl
    ex
    exlimdv
    syl5bi
    @24
    @14
    c0
    wceq
    #
    @15
    @12
    uni0b
    @38
    @15
    c0
    @6
    wcel
    @5
    @6
    c0
    @5
    cF
    ssun2
    c0
    0ex
    snid
    sselii
    #
    @14
    c0
    @6
    eleq1
    mpbiri
    sylbir
    pm2.61d2
    ex
    alrimiv
    @4
    @21
    vx
    cF
    wral
    @21
    vx
    @5
    wral
    @22
    @4
    @21
    vx
    cF
    @4
    @12
    cF
    wcel
    #
    wa
    #
    @20
    vy
    cF
    wral
    @20
    vy
    @5
    wral
    @21
    @41
    @20
    vy
    cF
    @4
    @40
    @31
    @20
    @4
    @40
    @31
    w3a
    @19
    cF
    wcel
    @20
    @12
    @18
    cF
    @2
    filin
    @19
    cF
    @5
    elun1
    syl
    3expa
    ralrimiva
    @20
    vy
    @5
    @26
    @18
    c0
    wceq
    #
    @20
    @18
    c0
    elsni
    @42
    @19
    c0
    @6
    @42
    @19
    @12
    c0
    cin
    c0
    @18
    c0
    @12
    ineq2
    @12
    in0
    syl6eq
    @39
    syl6eqel
    syl
    rgen
    @20
    vy
    cF
    @5
    ralun
    sylancl
    ralrimiva
    @21
    vx
    @5
    @12
    @5
    wcel
    #
    @12
    c0
    wceq
    #
    @21
    @12
    c0
    elsni
    #
    @44
    @20
    vy
    @6
    @44
    @19
    c0
    @6
    @44
    @19
    c0
    @18
    cin
    c0
    @12
    c0
    @18
    ineq1
    @18
    0in
    syl6eq
    @39
    syl6eqel
    ralrimivw
    syl
    rgen
    @21
    vx
    cF
    @5
    ralun
    sylancl
    @4
    @6
    cvv
    wcel
    #
    @8
    @17
    @22
    wa
    wb
    @4
    @5
    cvv
    wcel
    @46
    p0ex
    cF
    @5
    @3
    cvv
    unexg
    mpan2
    vx
    vy
    cvv
    @6
    istopg
    syl
    mpbir2and
    @4
    vx
    @10
    @11
    @4
    @12
    @6
    wcel
    #
    @12
    @9
    wcel
    #
    wa
    @44
    @12
    @2
    wceq
    #
    wo
    #
    @12
    @10
    wcel
    @12
    @11
    wcel
    @4
    @47
    @48
    @50
    @48
    @2
    @12
    cdif
    #
    cF
    wcel
    #
    @51
    @5
    wcel
    #
    wo
    #
    @4
    @47
    wa
    #
    @50
    @48
    @51
    @6
    wcel
    @54
    @12
    @6
    @2
    @37
    cldopn
    @51
    cF
    @5
    elun
    sylib
    @55
    @52
    @44
    @53
    @49
    @4
    @47
    @52
    @44
    wi
    #
    @47
    @40
    @43
    wo
    @4
    @56
    @12
    cF
    @5
    elun
    @4
    @40
    @56
    @43
    @4
    @40
    @56
    @41
    @52
    @44
    @4
    cF
    @2
    cfbas
    cfv
    wcel
    @40
    @52
    wn
    cF
    @2
    filfbas
    @12
    @2
    cF
    @2
    fbncp
    sylan
    pm2.21d
    ex
    @4
    @43
    @52
    @44
    @45
    a1i13
    jaod
    syl5bi
    imp
    @53
    @51
    c0
    wceq
    #
    @55
    @49
    @51
    c0
    elsni
    @55
    @12
    @2
    wss
    #
    @57
    @2
    @12
    wss
    #
    @49
    @47
    @58
    @4
    @47
    @12
    @35
    @2
    @12
    @6
    elssuni
    @37
    syl6sseqr
    adantl
    @59
    @57
    @2
    @12
    ssdif0
    biimpri
    @49
    @58
    @59
    @12
    @2
    eqss
    simplbi2
    syl2im
    syl5
    orim12d
    syl5
    expimpd
    @12
    @6
    @9
    elin
    @12
    c0
    @2
    vx
    vex
    elpr
    3imtr4g
    ssrdv
    @6
    @2
    @37
    isconn2
    sylanbrc
    syl
end
