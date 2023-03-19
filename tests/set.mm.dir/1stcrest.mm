include "c1stc.mm"
include "wcel.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "ctop.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wss.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cpw.mm"
include "cuni.mm"
include "1stctop.mm"
include "resttop.mm"
include "sylan.mm"
include "cin.mm"
include "wceq.mm"
include "eqid.mm"
include "restuni2.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "simpl.mm"
include "inss2.mm"
include "sseli.mm"
include "1stcclb.mm"
include "syl2an.mm"
include "simplll.mm"
include "elpwi.mm"
include "ad2antrl.mm"
include "ssrest.mm"
include "syl2anc.mm"
include "ovex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "cmpt.mm"
include "crn.mm"
include "cvv.mm"
include "vex.mm"
include "simpllr.mm"
include "restval.mm"
include "sylancr.mm"
include "simprrl.mm"
include "1stcrestlem.mm"
include "syl.mm"
include "eqbrtrd.mm"
include "wb.mm"
include "ad3antrrr.mm"
include "elrest.mm"
include "r19.29.mm"
include "simprr.mm"
include "a1d.mm"
include "ancld.mm"
include "elin.mm"
include "syl6ibr.mm"
include "ssrin.mm"
include "a1i.mm"
include "anim12d.mm"
include "reximdv.mm"
include "inex1.mm"
include "simp-4r.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "adantl.mm"
include "rexxfr2d.mm"
include "sylibrd.mm"
include "expr.mm"
include "com23.mm"
include "imim2d.mm"
include "imp4b.mm"
include "syl6bb.mm"
include "sseq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "rexlimdva.mm"
include "syl5.mm"
include "expd.mm"
include "impr.mm"
include "adantrrl.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "breq1.mm"
include "rexeq.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rexlimddv.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "is1stc2.mm"
include "sylanbrc.mm"

theorem 1stcrest
  let cA: class A
  let cJ: class J
  let cV: class V
  let va: setvar a
  let vt: setvar t
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B


  assert |- ( ( J e. 1stc /\ A e. V ) -> ( J |`t A ) e. 1stc )

  proof
    cJ
    c1stc
    wcel
    #
    cA
    cV
    wcel
    #
    wa
    #
    cJ
    cA
    crest
    co
    #
    ctop
    wcel
    #
    vy
    cv
    #
    com
    cdom
    wbr
    #
    vx
    cv
    #
    vz
    cv
    #
    wcel
    #
    @7
    vw
    cv
    #
    wcel
    #
    @10
    @8
    wss
    #
    wa
    #
    vw
    @5
    wrex
    #
    wi
    #
    vz
    @3
    wral
    #
    wa
    #
    vy
    @3
    cpw
    #
    wrex
    #
    vx
    @3
    cuni
    #
    wral
    @3
    c1stc
    wcel
    @0
    cJ
    ctop
    wcel
    #
    @1
    @4
    cJ
    1stctop
    #
    cA
    cJ
    cV
    resttop
    sylan
    @2
    @19
    vx
    @20
    @2
    @7
    @20
    wcel
    #
    @7
    cA
    cJ
    cuni
    #
    cin
    #
    wcel
    #
    @19
    @2
    @26
    @23
    @2
    @25
    @20
    @7
    @0
    @21
    @1
    @25
    @20
    wceq
    @22
    cA
    cJ
    cV
    @24
    @24
    eqid
    #
    restuni2
    sylan
    eleq2d
    biimpar
    @2
    @26
    wa
    #
    vt
    cv
    #
    com
    cdom
    wbr
    #
    @7
    va
    cv
    #
    wcel
    #
    @7
    @5
    wcel
    #
    @5
    @31
    wss
    #
    wa
    #
    vy
    @29
    wrex
    #
    wi
    #
    va
    cJ
    wral
    #
    wa
    #
    @19
    vt
    cJ
    cpw
    #
    @2
    @0
    @7
    @24
    wcel
    @39
    vt
    @40
    wrex
    @26
    @0
    @1
    simpl
    @25
    @24
    @7
    cA
    @24
    inss2
    sseli
    vt
    va
    vy
    @7
    cJ
    @24
    @27
    1stcclb
    syl2an
    @28
    @29
    @40
    wcel
    #
    @39
    wa
    #
    wa
    #
    @29
    cA
    crest
    co
    #
    @18
    wcel
    #
    @44
    com
    cdom
    wbr
    #
    @9
    @13
    vw
    @44
    wrex
    #
    wi
    #
    vz
    @3
    wral
    #
    @19
    @43
    @44
    @3
    wss
    #
    @45
    @43
    @0
    @29
    cJ
    wss
    #
    @50
    @0
    @1
    @26
    @42
    simplll
    @41
    @51
    @28
    @39
    @29
    cJ
    elpwi
    ad2antrl
    cA
    @29
    cJ
    c1stc
    ssrest
    syl2anc
    @44
    @3
    cJ
    cA
    crest
    ovex
    elpw2
    sylibr
    @43
    @44
    vv
    @29
    vv
    cv
    cA
    cin
    #
    cmpt
    crn
    #
    com
    cdom
    @43
    @29
    cvv
    wcel
    #
    @1
    @44
    @53
    wceq
    vt
    vex
    #
    @0
    @1
    @26
    @42
    simpllr
    #
    vv
    cA
    @29
    cvv
    cV
    restval
    sylancr
    @43
    @30
    @53
    com
    cdom
    wbr
    @28
    @41
    @30
    @38
    simprrl
    vv
    @29
    @52
    1stcrestlem
    syl
    eqbrtrd
    @43
    @48
    vz
    @3
    @43
    @8
    @3
    wcel
    #
    @8
    @31
    cA
    cin
    #
    wceq
    #
    va
    cJ
    wrex
    #
    @48
    @43
    @21
    @1
    @57
    @60
    wb
    @0
    @21
    @1
    @26
    @42
    @22
    ad3antrrr
    @56
    va
    @8
    cA
    cJ
    ctop
    cV
    elrest
    syl2anc
    @28
    @41
    @38
    @60
    @48
    wi
    #
    @30
    @28
    @41
    @38
    @61
    @28
    @41
    wa
    #
    @38
    @60
    @48
    @38
    @60
    wa
    @37
    @59
    wa
    #
    va
    cJ
    wrex
    @62
    @48
    @37
    @59
    va
    cJ
    r19.29
    @62
    @63
    @48
    va
    cJ
    @62
    @31
    cJ
    wcel
    #
    wa
    #
    @37
    @59
    @48
    @65
    @37
    wa
    @48
    @59
    @32
    @7
    cA
    wcel
    #
    wa
    #
    @11
    @10
    @58
    wss
    #
    wa
    #
    vw
    @44
    wrex
    #
    wi
    @65
    @37
    @32
    @66
    @70
    @65
    @36
    @66
    @70
    wi
    @32
    @65
    @66
    @36
    @70
    @62
    @64
    @66
    @36
    @70
    wi
    @62
    @64
    @66
    wa
    #
    wa
    #
    @36
    @7
    @5
    cA
    cin
    #
    wcel
    #
    @73
    @58
    wss
    #
    wa
    #
    vy
    @29
    wrex
    @70
    @72
    @35
    @76
    vy
    @29
    @72
    @33
    @74
    @34
    @75
    @72
    @33
    @33
    @66
    wa
    @74
    @72
    @33
    @66
    @72
    @66
    @33
    @62
    @64
    @66
    simprr
    a1d
    ancld
    @7
    @5
    cA
    elin
    syl6ibr
    @34
    @75
    wi
    @72
    @5
    @31
    cA
    ssrin
    a1i
    anim12d
    reximdv
    @72
    @69
    @76
    vw
    vy
    @73
    @44
    @29
    cvv
    @73
    cvv
    wcel
    @72
    @5
    @29
    wcel
    wa
    @5
    cA
    vy
    vex
    inex1
    a1i
    @72
    @54
    @1
    @10
    @44
    wcel
    @10
    @73
    wceq
    #
    vy
    @29
    wrex
    wb
    @55
    @0
    @1
    @26
    @41
    @71
    simp-4r
    vy
    @10
    cA
    @29
    cvv
    cV
    elrest
    sylancr
    @77
    @69
    @76
    wb
    @72
    @77
    @11
    @74
    @68
    @75
    @10
    @73
    @7
    eleq2
    @10
    @73
    @58
    sseq1
    anbi12d
    adantl
    rexxfr2d
    sylibrd
    expr
    com23
    imim2d
    imp4b
    @59
    @9
    @67
    @47
    @70
    @59
    @9
    @7
    @58
    wcel
    @67
    @8
    @58
    @7
    eleq2
    @7
    @31
    cA
    elin
    syl6bb
    @59
    @13
    @69
    vw
    @44
    @59
    @12
    @68
    @11
    @8
    @58
    @10
    sseq2
    anbi2d
    rexbidv
    imbi12d
    syl5ibrcom
    expimpd
    rexlimdva
    syl5
    expd
    impr
    adantrrl
    sylbid
    ralrimiv
    @17
    @46
    @49
    wa
    vy
    @44
    @18
    @5
    @44
    wceq
    #
    @6
    @46
    @16
    @49
    @5
    @44
    com
    cdom
    breq1
    @78
    @15
    @48
    vz
    @3
    @78
    @14
    @47
    @9
    @13
    vw
    @5
    @44
    rexeq
    imbi2d
    ralbidv
    anbi12d
    rspcev
    syl12anc
    rexlimddv
    syldan
    ralrimiva
    vx
    vy
    vz
    vw
    @3
    @20
    @20
    eqid
    is1stc2
    sylanbrc
end
