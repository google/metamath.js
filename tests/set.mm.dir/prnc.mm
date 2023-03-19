include "ccring.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cigen.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "crab.mm"
include "cidl.mm"
include "cfv.mm"
include "wss.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "cgi.mm"
include "crngo.mm"
include "crngorngo.mm"
include "ssrab2.mm"
include "a1i.mm"
include "eqid.mm"
include "rngo0cl.mm"
include "adantr.mm"
include "rngolz.mm"
include "eqcomd.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "rngodir.mm"
include "3exp2.mm"
include "imp42.mm"
include "rngogcl.mm"
include "3expib.mm"
include "imdistani.mm"
include "rngocl.mm"
include "3expa.mm"
include "mpan2.mm"
include "ad2antlr.mm"
include "sylan.mm"
include "eqeltrrd.mm"
include "an32s.mm"
include "anassrs.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "adantld.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "rngoass.mm"
include "anass1rs.mm"
include "ralrimiva.mm"
include "jca.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "3jca.mm"
include "wb.mm"
include "isidlc.mm"
include "mpbird.mm"
include "simpr.mm"
include "crn.mm"
include "c1st.mm"
include "rneqi.mm"
include "eqtri.mm"
include "rngo1cl.mm"
include "rngolidm.mm"
include "snssd.mm"
include "snssg.mm"
include "biimpar.mm"
include "idllmulcl.mm"
include "eleq1.mm"
include "rabss.mm"
include "sylibr.mm"
include "ex.mm"
include "syl5.mm"
include "expdimp.mm"
include "snssi.mm"
include "igenval2.mm"
include "syl2an.mm"

theorem prnc
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cG: class G
  let cH: class H
  let cX: class X
  let vj: setvar j
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vr: setvar r
  let vs: setvar s
  assume prnc.1: |- G = ( 1st ` R )
  assume prnc.2: |- H = ( 2nd ` R )
  assume prnc.3: |- X = ran G

  disjoint R x
  disjoint R y
  disjoint x y
  disjoint X x
  disjoint X y
  disjoint G x
  disjoint G y
  disjoint H x
  disjoint H y
  disjoint A x
  disjoint A y
  disjoint R j
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R r
  disjoint R s
  disjoint j x
  disjoint j y
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j r
  disjoint j s
  disjoint u x
  disjoint v x
  disjoint w x
  disjoint r x
  disjoint s x
  disjoint u y
  disjoint v y
  disjoint w y
  disjoint r y
  disjoint s y
  disjoint u v
  disjoint u w
  disjoint r u
  disjoint s u
  disjoint v w
  disjoint r v
  disjoint s v
  disjoint r w
  disjoint s w
  disjoint r s
  disjoint X j
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X r
  disjoint X s
  disjoint G r
  disjoint G s
  disjoint H j
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint H r
  disjoint H s
  disjoint A j
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A r
  disjoint A s
  assert |- ( ( R e. CRingOps /\ A e. X ) -> ( R IdlGen { A } ) = { x e. X | E. y e. X x = ( y H A ) } )

  proof
    cR
    ccring
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cR
    cA
    csn
    #
    cigen
    co
    vx
    cv
    #
    vy
    cv
    #
    cA
    cH
    co
    #
    wceq
    #
    vy
    cX
    wrex
    #
    vx
    cX
    crab
    #
    wceq
    #
    @9
    cR
    cidl
    cfv
    #
    wcel
    #
    @3
    @9
    wss
    #
    @3
    vj
    cv
    #
    wss
    #
    @9
    @14
    wss
    #
    wi
    #
    vj
    @11
    wral
    #
    w3a
    #
    @2
    @12
    @13
    @18
    @2
    @12
    @9
    cX
    wss
    #
    cG
    cgi
    cfv
    #
    @9
    wcel
    #
    vu
    cv
    #
    vv
    cv
    #
    cG
    co
    #
    @9
    wcel
    #
    vv
    @9
    wral
    #
    vw
    cv
    #
    @23
    cH
    co
    #
    @9
    wcel
    #
    vw
    cX
    wral
    #
    wa
    #
    vu
    @9
    wral
    #
    w3a
    #
    @0
    cR
    crngo
    wcel
    #
    @1
    @34
    cR
    crngorngo
    #
    @35
    @1
    wa
    #
    @20
    @22
    @33
    @20
    @37
    @8
    vx
    cX
    ssrab2
    a1i
    @37
    @21
    cX
    wcel
    #
    @21
    @6
    wceq
    #
    vy
    cX
    wrex
    #
    @22
    @35
    @38
    @1
    cR
    cG
    cX
    @21
    prnc.1
    prnc.3
    @21
    eqid
    #
    rngo0cl
    adantr
    #
    @37
    @38
    @21
    @21
    cA
    cH
    co
    #
    wceq
    #
    @40
    @42
    @37
    @43
    @21
    cA
    cR
    cG
    cH
    cX
    @21
    @41
    prnc.3
    prnc.1
    prnc.2
    rngolz
    eqcomd
    @39
    @44
    vy
    @21
    cX
    @5
    @21
    wceq
    @6
    @43
    @21
    @5
    @21
    cA
    cH
    oveq1
    eqeq2d
    rspcev
    syl2anc
    @8
    @40
    vx
    @21
    cX
    @4
    @21
    wceq
    @7
    @39
    vy
    cX
    @4
    @21
    @6
    eqeq1
    rexbidv
    elrab
    sylanbrc
    @37
    @32
    vu
    @9
    @23
    @9
    wcel
    @23
    cX
    wcel
    #
    @23
    vr
    cv
    #
    cA
    cH
    co
    #
    wceq
    #
    vr
    cX
    wrex
    #
    wa
    @37
    @32
    @8
    @49
    vx
    @23
    cX
    @4
    @23
    wceq
    #
    @8
    @23
    @6
    wceq
    #
    vy
    cX
    wrex
    @49
    @50
    @7
    @51
    vy
    cX
    @4
    @23
    @6
    eqeq1
    rexbidv
    @51
    @48
    vy
    vr
    cX
    @5
    @46
    wceq
    @6
    @47
    @23
    @5
    @46
    cA
    cH
    oveq1
    eqeq2d
    cbvrexv
    syl6bb
    elrab
    @37
    @49
    @32
    @45
    @37
    @48
    @32
    vr
    cX
    @37
    @46
    cX
    wcel
    #
    wa
    #
    @32
    @48
    @47
    @24
    cG
    co
    #
    @9
    wcel
    #
    vv
    @9
    wral
    #
    @28
    @47
    cH
    co
    #
    @9
    wcel
    #
    vw
    cX
    wral
    #
    wa
    @53
    @56
    @59
    @53
    @55
    vv
    @9
    @24
    @9
    wcel
    @24
    cX
    wcel
    #
    @24
    vs
    cv
    #
    cA
    cH
    co
    #
    wceq
    #
    vs
    cX
    wrex
    #
    wa
    @53
    @55
    @8
    @64
    vx
    @24
    cX
    @4
    @24
    wceq
    #
    @8
    @24
    @6
    wceq
    #
    vy
    cX
    wrex
    @64
    @65
    @7
    @66
    vy
    cX
    @4
    @24
    @6
    eqeq1
    rexbidv
    @66
    @63
    vy
    vs
    cX
    @5
    @61
    wceq
    @6
    @62
    @24
    @5
    @61
    cA
    cH
    oveq1
    eqeq2d
    cbvrexv
    syl6bb
    elrab
    @53
    @64
    @55
    @60
    @53
    @63
    @55
    vs
    cX
    @53
    @61
    cX
    wcel
    #
    wa
    @55
    @63
    @47
    @62
    cG
    co
    #
    @9
    wcel
    #
    @37
    @52
    @67
    @69
    @35
    @52
    @67
    wa
    #
    @1
    @69
    @35
    @70
    wa
    #
    @1
    wa
    @46
    @61
    cG
    co
    #
    cA
    cH
    co
    #
    @68
    @9
    @35
    @52
    @67
    @1
    @73
    @68
    wceq
    #
    @35
    @52
    @67
    @1
    @74
    @46
    @61
    cA
    cR
    cG
    cH
    cX
    prnc.1
    prnc.2
    prnc.3
    rngodir
    3exp2
    imp42
    @71
    @35
    @72
    cX
    wcel
    #
    wa
    #
    @1
    @73
    @9
    wcel
    #
    @35
    @70
    @75
    @35
    @52
    @67
    @75
    @46
    @61
    cR
    cG
    cX
    prnc.1
    prnc.3
    rngogcl
    3expib
    imdistani
    @76
    @1
    wa
    @73
    cX
    wcel
    #
    @73
    @6
    wceq
    #
    vy
    cX
    wrex
    #
    @77
    @35
    @75
    @1
    @78
    @72
    cA
    cR
    cG
    cH
    cX
    prnc.1
    prnc.2
    prnc.3
    rngocl
    3expa
    @75
    @80
    @35
    @1
    @75
    @73
    @73
    wceq
    #
    @80
    @73
    eqid
    @79
    @81
    vy
    @72
    cX
    @5
    @72
    wceq
    @6
    @73
    @73
    @5
    @72
    cA
    cH
    oveq1
    eqeq2d
    rspcev
    mpan2
    ad2antlr
    @8
    @80
    vx
    @73
    cX
    @4
    @73
    wceq
    @7
    @79
    vy
    cX
    @4
    @73
    @6
    eqeq1
    rexbidv
    elrab
    sylanbrc
    sylan
    eqeltrrd
    an32s
    anassrs
    @63
    @54
    @68
    @9
    @24
    @62
    @47
    cG
    oveq2
    eleq1d
    syl5ibrcom
    rexlimdva
    adantld
    syl5bi
    ralrimiv
    @53
    @58
    vw
    cX
    @37
    @28
    cX
    wcel
    #
    @52
    @58
    @37
    @82
    @52
    wa
    #
    wa
    @28
    @46
    cH
    co
    #
    cA
    cH
    co
    #
    @57
    @9
    @35
    @83
    @1
    @85
    @57
    wceq
    #
    @35
    @82
    @52
    @1
    @86
    @35
    @82
    @52
    @1
    @86
    @28
    @46
    cA
    cR
    cG
    cH
    cX
    prnc.1
    prnc.2
    prnc.3
    rngoass
    3exp2
    imp42
    an32s
    @35
    @83
    @1
    @85
    @9
    wcel
    #
    @35
    @83
    wa
    @35
    @84
    cX
    wcel
    #
    wa
    #
    @1
    @87
    @35
    @83
    @88
    @35
    @82
    @52
    @88
    @28
    @46
    cR
    cG
    cH
    cX
    prnc.1
    prnc.2
    prnc.3
    rngocl
    3expib
    imdistani
    @89
    @1
    wa
    @85
    cX
    wcel
    #
    @85
    @6
    wceq
    #
    vy
    cX
    wrex
    #
    @87
    @35
    @88
    @1
    @90
    @84
    cA
    cR
    cG
    cH
    cX
    prnc.1
    prnc.2
    prnc.3
    rngocl
    3expa
    @88
    @92
    @35
    @1
    @88
    @85
    @85
    wceq
    #
    @92
    @85
    eqid
    @91
    @93
    vy
    @84
    cX
    @5
    @84
    wceq
    @6
    @85
    @85
    @5
    @84
    cA
    cH
    oveq1
    eqeq2d
    rspcev
    mpan2
    ad2antlr
    @8
    @92
    vx
    @85
    cX
    @4
    @85
    wceq
    @7
    @91
    vy
    cX
    @4
    @85
    @6
    eqeq1
    rexbidv
    elrab
    sylanbrc
    sylan
    an32s
    eqeltrrd
    anass1rs
    ralrimiva
    jca
    @48
    @27
    @56
    @31
    @59
    @48
    @26
    @55
    vv
    @9
    @48
    @25
    @54
    @9
    @23
    @47
    @24
    cG
    oveq1
    eleq1d
    ralbidv
    @48
    @30
    @58
    vw
    cX
    @48
    @29
    @57
    @9
    @23
    @47
    @28
    cH
    oveq2
    eleq1d
    ralbidv
    anbi12d
    syl5ibrcom
    rexlimdva
    adantld
    syl5bi
    ralrimiv
    3jca
    sylan
    @0
    @12
    @34
    wb
    @1
    vu
    vv
    vw
    cR
    cG
    cH
    @9
    cX
    @21
    prnc.1
    prnc.2
    prnc.3
    @41
    isidlc
    adantr
    mpbird
    @2
    cA
    @9
    @2
    @1
    cA
    @6
    wceq
    #
    vy
    cX
    wrex
    #
    cA
    @9
    wcel
    @0
    @1
    simpr
    @0
    @35
    @1
    @95
    @36
    @37
    cH
    cgi
    cfv
    #
    cX
    wcel
    #
    cA
    @96
    cA
    cH
    co
    #
    wceq
    #
    @95
    @35
    @97
    @1
    cR
    @96
    cH
    cX
    cX
    cG
    crn
    cR
    c1st
    cfv
    #
    crn
    prnc.3
    cG
    @100
    prnc.1
    rneqi
    eqtri
    #
    prnc.2
    @96
    eqid
    #
    rngo1cl
    adantr
    @37
    @98
    cA
    cA
    cR
    @96
    cH
    cX
    prnc.2
    @101
    @102
    rngolidm
    eqcomd
    @94
    @99
    vy
    @96
    cX
    @5
    @96
    wceq
    @6
    @98
    cA
    @5
    @96
    cA
    cH
    oveq1
    eqeq2d
    rspcev
    syl2anc
    sylan
    @8
    @95
    vx
    cA
    cX
    @4
    cA
    wceq
    @7
    @94
    vy
    cX
    @4
    cA
    @6
    eqeq1
    rexbidv
    elrab
    sylanbrc
    snssd
    @0
    @35
    @1
    @18
    @36
    @37
    @17
    vj
    @11
    @35
    @14
    @11
    wcel
    #
    @1
    @17
    @35
    @103
    wa
    #
    @1
    @15
    @16
    @1
    @15
    wa
    cA
    @14
    wcel
    #
    @104
    @16
    @1
    @105
    @15
    cA
    @14
    cX
    snssg
    biimpar
    @104
    @105
    @16
    @104
    @105
    wa
    #
    @8
    @4
    @14
    wcel
    #
    wi
    #
    vx
    cX
    wral
    @16
    @106
    @108
    vx
    cX
    @106
    @108
    @4
    cX
    wcel
    @106
    @7
    @107
    vy
    cX
    @106
    @5
    cX
    wcel
    #
    wa
    @107
    @7
    @6
    @14
    wcel
    #
    @104
    @105
    @109
    @110
    cA
    @5
    cR
    cG
    cH
    @14
    cX
    prnc.1
    prnc.2
    prnc.3
    idllmulcl
    anassrs
    @4
    @6
    @14
    eleq1
    syl5ibrcom
    rexlimdva
    adantr
    ralrimiva
    @8
    vx
    cX
    @14
    rabss
    sylibr
    ex
    syl5
    expdimp
    an32s
    ralrimiva
    sylan
    3jca
    @0
    @35
    @3
    cX
    wss
    @10
    @19
    wb
    @1
    @36
    cA
    cX
    snssi
    cR
    @3
    vj
    cG
    @9
    cX
    prnc.1
    prnc.3
    igenval2
    syl2an
    mpbird
end
