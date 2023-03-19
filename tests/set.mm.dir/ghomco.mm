include "cgr.mm"
include "wcel.mm"
include "w3a.mm"
include "cghomOLD.mm"
include "co.mm"
include "wa.mm"
include "ccom.mm"
include "crn.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wi.mm"
include "fco.mm"
include "ancoms.mm"
include "ad2ant2r.mm"
include "a1i.mm"
include "ffvelrn.mm"
include "anim12da.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "rspc2va.mm"
include "sylan.mm"
include "an32s.mm"
include "adantllr.mm"
include "sylan9eq.mm"
include "anasss.mm"
include "fvco3.mm"
include "ad2ant2rl.mm"
include "oveq12d.mm"
include "adantlr.mm"
include "eqid.mm"
include "grpocl.mm"
include "3expb.mm"
include "sylan2.mm"
include "anassrs.mm"
include "3eqtr4d.mm"
include "expr.mm"
include "ralimdvva.mm"
include "ex.mm"
include "com23.mm"
include "imp.mm"
include "com12.mm"
include "3ad2ant1.mm"
include "jcad.mm"
include "wb.mm"
include "elghomOLD.mm"
include "3adant3.mm"
include "3adant1.mm"
include "anbi12d.mm"
include "3adant2.mm"
include "3imtr4d.mm"

theorem ghomco
  let cS: class S
  let cT: class T
  let cG: class G
  let cH: class H
  let cK: class K
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( G e. GrpOp /\ H e. GrpOp /\ K e. GrpOp ) /\ ( S e. ( G GrpOpHom H ) /\ T e. ( H GrpOpHom K ) ) ) -> ( T o. S ) e. ( G GrpOpHom K ) )

  proof
    cG
    cgr
    wcel
    #
    cH
    cgr
    wcel
    #
    cK
    cgr
    wcel
    #
    w3a
    #
    cS
    cG
    cH
    cghomOLD
    co
    wcel
    #
    cT
    cH
    cK
    cghomOLD
    co
    wcel
    #
    wa
    #
    cT
    cS
    ccom
    #
    cG
    cK
    cghomOLD
    co
    wcel
    #
    @3
    cG
    crn
    #
    cH
    crn
    #
    cS
    wf
    #
    vx
    cv
    #
    cS
    cfv
    #
    vy
    cv
    #
    cS
    cfv
    #
    cH
    co
    #
    @12
    @14
    cG
    co
    #
    cS
    cfv
    #
    wceq
    #
    vy
    @9
    wral
    vx
    @9
    wral
    #
    wa
    #
    @10
    cK
    crn
    #
    cT
    wf
    #
    vu
    cv
    #
    cT
    cfv
    #
    vv
    cv
    #
    cT
    cfv
    #
    cK
    co
    #
    @24
    @26
    cH
    co
    #
    cT
    cfv
    #
    wceq
    #
    vv
    @10
    wral
    vu
    @10
    wral
    #
    wa
    #
    wa
    #
    @9
    @22
    @7
    wf
    #
    @12
    @7
    cfv
    #
    @14
    @7
    cfv
    #
    cK
    co
    #
    @17
    @7
    cfv
    #
    wceq
    #
    vy
    @9
    wral
    vx
    @9
    wral
    #
    wa
    #
    @6
    @8
    @3
    @34
    @35
    @41
    @34
    @35
    wi
    @3
    @11
    @23
    @35
    @20
    @32
    @23
    @11
    @35
    @9
    @10
    @22
    cT
    cS
    fco
    ancoms
    ad2ant2r
    a1i
    @0
    @1
    @34
    @41
    wi
    @2
    @34
    @0
    @41
    @11
    @33
    @20
    @0
    @41
    wi
    #
    @11
    @33
    wa
    @20
    @43
    @11
    @23
    @32
    @20
    @43
    wi
    @11
    @23
    wa
    #
    @32
    wa
    #
    @0
    @20
    @41
    @45
    @0
    @20
    @41
    wi
    #
    @44
    @0
    @32
    @46
    @44
    @0
    wa
    #
    @32
    wa
    #
    @19
    @40
    vx
    vy
    @9
    @9
    @48
    @12
    @9
    wcel
    #
    @14
    @9
    wcel
    #
    wa
    #
    @19
    @40
    @48
    @51
    @19
    wa
    wa
    @13
    cT
    cfv
    #
    @15
    cT
    cfv
    #
    cK
    co
    #
    @18
    cT
    cfv
    #
    @38
    @39
    @48
    @51
    @19
    @54
    @55
    wceq
    @48
    @51
    wa
    @19
    @54
    @16
    cT
    cfv
    #
    @55
    @44
    @32
    @51
    @54
    @56
    wceq
    #
    @0
    @11
    @32
    @51
    @57
    @23
    @11
    @51
    @32
    @57
    @11
    @51
    wa
    @13
    @10
    wcel
    #
    @15
    @10
    wcel
    #
    wa
    @32
    @57
    @11
    @49
    @50
    @58
    @59
    @9
    @10
    @12
    cS
    ffvelrn
    @9
    @10
    @14
    cS
    ffvelrn
    anim12da
    @31
    @57
    @52
    @27
    cK
    co
    #
    @13
    @26
    cH
    co
    #
    cT
    cfv
    #
    wceq
    vu
    vv
    @13
    @15
    @10
    @10
    @24
    @13
    wceq
    #
    @28
    @60
    @30
    @62
    @63
    @25
    @52
    @27
    cK
    @24
    @13
    cT
    fveq2
    oveq1d
    @63
    @29
    @61
    cT
    @24
    @13
    @26
    cH
    oveq1
    fveq2d
    eqeq12d
    @26
    @15
    wceq
    #
    @60
    @54
    @62
    @56
    @64
    @27
    @53
    @52
    cK
    @26
    @15
    cT
    fveq2
    oveq2d
    @64
    @61
    @16
    cT
    @26
    @15
    @13
    cH
    oveq2
    fveq2d
    eqeq12d
    rspc2va
    sylan
    an32s
    adantllr
    adantllr
    @16
    @18
    cT
    fveq2
    sylan9eq
    anasss
    @47
    @51
    @38
    @54
    wceq
    #
    @32
    @19
    @44
    @51
    @65
    @0
    @44
    @51
    wa
    @36
    @52
    @37
    @53
    cK
    @11
    @49
    @36
    @52
    wceq
    @23
    @50
    @9
    @10
    @12
    cT
    cS
    fvco3
    ad2ant2r
    @11
    @50
    @37
    @53
    wceq
    @23
    @49
    @9
    @10
    @14
    cT
    cS
    fvco3
    ad2ant2rl
    oveq12d
    adantlr
    ad2ant2r
    @47
    @51
    @39
    @55
    wceq
    #
    @32
    @19
    @44
    @0
    @51
    @66
    @0
    @51
    wa
    @44
    @17
    @9
    wcel
    #
    @66
    @0
    @49
    @50
    @67
    @12
    @14
    cG
    @9
    @9
    eqid
    #
    grpocl
    3expb
    @11
    @67
    @66
    @23
    @9
    @10
    @17
    cT
    cS
    fvco3
    adantlr
    sylan2
    anassrs
    ad2ant2r
    3eqtr4d
    expr
    ralimdvva
    an32s
    ex
    com23
    anasss
    imp
    an32s
    com12
    3ad2ant1
    jcad
    @3
    @4
    @21
    @5
    @33
    @0
    @1
    @4
    @21
    wb
    @2
    vx
    vy
    cS
    cG
    cH
    @10
    @9
    @68
    @10
    eqid
    #
    elghomOLD
    3adant3
    @1
    @2
    @5
    @33
    wb
    @0
    vu
    vv
    cT
    cH
    cK
    @22
    @10
    @69
    @22
    eqid
    #
    elghomOLD
    3adant1
    anbi12d
    @0
    @2
    @8
    @42
    wb
    @1
    vx
    vy
    @7
    cG
    cK
    @22
    @9
    @68
    @70
    elghomOLD
    3adant2
    3imtr4d
    imp
end
