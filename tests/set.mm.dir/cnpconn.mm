include "cpconn.mm"
include "wcel.mm"
include "wfo.mm"
include "ccn.mm"
include "co.mm"
include "w3a.mm"
include "ctop.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "wa.mm"
include "cii.mm"
include "wrex.mm"
include "wral.mm"
include "cntop2.mm"
include "3ad2ant3.mm"
include "cuni.mm"
include "eqid.mm"
include "pconncn.mm"
include "3expb.mm"
include "3ad2antl1.mm"
include "ccom.mm"
include "simprl.mm"
include "simpll3.mm"
include "cnco.mm"
include "syl2anc.mm"
include "cicc.mm"
include "wf.mm"
include "iiuni.mm"
include "cnf.mm"
include "syl.mm"
include "0elunit.mm"
include "fvco3.mm"
include "sylancl.mm"
include "simprrl.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "1elunit.mm"
include "simprrr.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rexlimddv.mm"
include "ralrimivva.mm"
include "wb.mm"
include "crn.mm"
include "forn.mm"
include "3ad2ant2.mm"
include "dffo2.mm"
include "sylanbrc.mm"
include "eqeq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "cbvfo.mm"
include "ralbidv.mm"
include "mpbid.mm"
include "anbi1d.mm"
include "ispconn.mm"

theorem cnpconn
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  assume cnpconn.2: |- Y = U. K


  assert |- ( ( J e. PConn /\ F : X -onto-> Y /\ F e. ( J Cn K ) ) -> K e. PConn )

  proof
    cJ
    cpconn
    wcel
    #
    cX
    cY
    cF
    wfo
    #
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    w3a
    #
    cK
    ctop
    wcel
    #
    cc0
    vf
    cv
    #
    cfv
    #
    vx
    cv
    #
    wceq
    #
    c1
    @5
    cfv
    #
    vy
    cv
    #
    wceq
    #
    wa
    #
    vf
    cii
    cK
    ccn
    co
    #
    wrex
    #
    vy
    cY
    wral
    #
    vx
    cY
    wral
    #
    cK
    cpconn
    wcel
    @2
    @0
    @4
    @1
    cF
    cJ
    cK
    cntop2
    3ad2ant3
    @3
    @6
    vu
    cv
    #
    cF
    cfv
    #
    wceq
    #
    @11
    wa
    #
    vf
    @13
    wrex
    #
    vy
    cY
    wral
    #
    vu
    cJ
    cuni
    #
    wral
    #
    @16
    @3
    @19
    @9
    vv
    cv
    #
    cF
    cfv
    #
    wceq
    #
    wa
    #
    vf
    @13
    wrex
    #
    vv
    @23
    wral
    #
    vu
    @23
    wral
    @24
    @3
    @29
    vu
    vv
    @23
    @23
    @3
    @17
    @23
    wcel
    #
    @25
    @23
    wcel
    #
    wa
    #
    wa
    #
    cc0
    vg
    cv
    #
    cfv
    #
    @17
    wceq
    #
    c1
    @35
    cfv
    #
    @25
    wceq
    #
    wa
    #
    @29
    vg
    cii
    cJ
    ccn
    co
    #
    @0
    @1
    @33
    @40
    vg
    @41
    wrex
    #
    @2
    @0
    @31
    @32
    @42
    @17
    @25
    vg
    cJ
    @23
    @23
    eqid
    #
    pconncn
    3expb
    3ad2antl1
    @34
    @35
    @41
    wcel
    #
    @40
    wa
    #
    wa
    #
    cF
    @35
    ccom
    #
    @13
    wcel
    #
    cc0
    @47
    cfv
    #
    @18
    wceq
    #
    c1
    @47
    cfv
    #
    @26
    wceq
    #
    @29
    @46
    @44
    @2
    @48
    @34
    @44
    @40
    simprl
    #
    @0
    @1
    @2
    @33
    @45
    simpll3
    @35
    cF
    cii
    cJ
    cK
    cnco
    syl2anc
    @46
    @49
    @36
    cF
    cfv
    #
    @18
    @46
    cc0
    c1
    cicc
    co
    #
    @23
    @35
    wf
    #
    cc0
    @55
    wcel
    @49
    @54
    wceq
    @46
    @44
    @56
    @53
    @35
    cii
    cJ
    @55
    @23
    iiuni
    @43
    cnf
    syl
    #
    0elunit
    @55
    @23
    cc0
    cF
    @35
    fvco3
    sylancl
    @46
    @36
    @17
    cF
    @34
    @44
    @37
    @39
    simprrl
    fveq2d
    eqtrd
    @46
    @51
    @38
    cF
    cfv
    #
    @26
    @46
    @56
    c1
    @55
    wcel
    @51
    @58
    wceq
    @57
    1elunit
    @55
    @23
    c1
    cF
    @35
    fvco3
    sylancl
    @46
    @38
    @25
    cF
    @34
    @44
    @37
    @39
    simprrr
    fveq2d
    eqtrd
    @28
    @50
    @52
    wa
    vf
    @47
    @13
    @5
    @47
    wceq
    #
    @19
    @50
    @27
    @52
    @59
    @6
    @49
    @18
    cc0
    @5
    @47
    fveq1
    eqeq1d
    @59
    @9
    @51
    @26
    c1
    @5
    @47
    fveq1
    eqeq1d
    anbi12d
    rspcev
    syl12anc
    rexlimddv
    ralrimivva
    @3
    @30
    @22
    vu
    @23
    @3
    @23
    cY
    cF
    wfo
    #
    @30
    @22
    wb
    @3
    @23
    cY
    cF
    wf
    #
    cF
    crn
    cY
    wceq
    #
    @60
    @2
    @0
    @61
    @1
    cF
    cJ
    cK
    @23
    cY
    @43
    cnpconn.2
    cnf
    3ad2ant3
    @1
    @0
    @62
    @2
    cX
    cY
    cF
    forn
    3ad2ant2
    @23
    cY
    cF
    dffo2
    sylanbrc
    #
    @29
    @21
    vv
    vy
    @23
    cY
    cF
    @26
    @10
    wceq
    #
    @28
    @20
    vf
    @13
    @64
    @27
    @11
    @19
    @26
    @10
    @9
    eqeq2
    anbi2d
    rexbidv
    cbvfo
    syl
    ralbidv
    mpbid
    @3
    @60
    @24
    @16
    wb
    @63
    @22
    @15
    vu
    vx
    @23
    cY
    cF
    @18
    @7
    wceq
    #
    @21
    @14
    vy
    cY
    @65
    @20
    @12
    vf
    @13
    @65
    @19
    @8
    @11
    @18
    @7
    @6
    eqeq2
    anbi1d
    rexbidv
    ralbidv
    cbvfo
    syl
    mpbid
    vx
    vy
    vf
    cK
    cY
    cnpconn.2
    ispconn
    sylanbrc
end
