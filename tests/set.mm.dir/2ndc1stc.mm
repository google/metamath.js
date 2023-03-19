include "c2ndc.mm"
include "wcel.mm"
include "ctop.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cpw.mm"
include "cuni.mm"
include "c1stc.mm"
include "2ndctop.mm"
include "ctg.mm"
include "cfv.mm"
include "wceq.mm"
include "ctb.mm"
include "is2ndc.mm"
include "w3a.mm"
include "crab.mm"
include "ssrab2.mm"
include "bastg.mm"
include "3ad2ant1.mm"
include "syl5ss.mm"
include "fvex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "cvv.mm"
include "vex.mm"
include "ssdomg.mm"
include "mp2.mm"
include "simp2.mm"
include "domtr.mm"
include "sylancr.mm"
include "wb.mm"
include "eltg2b.mm"
include "elequ1.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "rspccv.mm"
include "id.mm"
include "adantrr.mm"
include "elequ2.mm"
include "elrab.mm"
include "adantl.mm"
include "simprr.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexlimdvaa.mm"
include "syl9r.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "breq1.mm"
include "rexeq.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "syl12anc.mm"
include "3expia.mm"
include "unieq.mm"
include "eleq2d.mm"
include "pweq.mm"
include "raleq.mm"
include "anbi2d.mm"
include "rexeqbidv.mm"
include "imbi12d.mm"
include "syl5ibcom.mm"
include "expimpd.mm"
include "rexlimiv.mm"
include "sylbi.mm"
include "eqid.mm"
include "is1stc2.mm"
include "sylanbrc.mm"

theorem 2ndc1stc
  let cJ: class J
  let vb: setvar b
  let vo: setvar o
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y


  assert |- ( J e. 2ndc -> J e. 1stc )

  proof
    cJ
    c2ndc
    wcel
    #
    cJ
    ctop
    wcel
    vs
    cv
    #
    com
    cdom
    wbr
    #
    vx
    cv
    #
    vo
    cv
    #
    wcel
    #
    @3
    vp
    cv
    #
    wcel
    #
    @6
    @4
    wss
    #
    wa
    #
    vp
    @1
    wrex
    #
    wi
    #
    vo
    cJ
    wral
    #
    wa
    #
    vs
    cJ
    cpw
    #
    wrex
    #
    vx
    cJ
    cuni
    #
    wral
    cJ
    c1stc
    wcel
    cJ
    2ndctop
    @0
    @15
    vx
    @16
    @0
    vb
    cv
    #
    com
    cdom
    wbr
    #
    @17
    ctg
    cfv
    #
    cJ
    wceq
    #
    wa
    #
    vb
    ctb
    wrex
    @3
    @16
    wcel
    #
    @15
    wi
    #
    vb
    cJ
    is2ndc
    @21
    @23
    vb
    ctb
    @17
    ctb
    wcel
    #
    @18
    @20
    @23
    @24
    @18
    wa
    @3
    @19
    cuni
    #
    wcel
    #
    @2
    @11
    vo
    @19
    wral
    #
    wa
    #
    vs
    @19
    cpw
    #
    wrex
    #
    wi
    @20
    @23
    @24
    @18
    @26
    @30
    @24
    @18
    @26
    w3a
    #
    @3
    vq
    cv
    wcel
    #
    vq
    @17
    crab
    #
    @29
    wcel
    #
    @33
    com
    cdom
    wbr
    #
    @5
    @9
    vp
    @33
    wrex
    #
    wi
    #
    vo
    @19
    wral
    #
    @30
    @31
    @33
    @19
    wss
    @34
    @31
    @33
    @17
    @19
    @32
    vq
    @17
    ssrab2
    #
    @24
    @18
    @17
    @19
    wss
    @26
    @17
    ctb
    bastg
    3ad2ant1
    syl5ss
    @33
    @19
    @17
    ctg
    fvex
    elpw2
    sylibr
    @31
    @33
    @17
    cdom
    wbr
    #
    @18
    @35
    @17
    cvv
    wcel
    @33
    @17
    wss
    @40
    vb
    vex
    @39
    @33
    @17
    cvv
    ssdomg
    mp2
    @24
    @18
    @26
    simp2
    @33
    @17
    com
    domtr
    sylancr
    @31
    @37
    vo
    @19
    @31
    @4
    @19
    wcel
    #
    vy
    cv
    #
    vt
    cv
    #
    wcel
    #
    @43
    @4
    wss
    #
    wa
    #
    vt
    @17
    wrex
    #
    vy
    @4
    wral
    #
    @37
    @24
    @18
    @41
    @48
    wb
    @26
    vy
    vt
    @4
    @17
    ctb
    eltg2b
    3ad2ant1
    @48
    @5
    @3
    @43
    wcel
    #
    @45
    wa
    #
    vt
    @17
    wrex
    #
    @31
    @36
    @47
    @51
    vy
    @3
    @4
    @42
    @3
    wceq
    #
    @46
    @50
    vt
    @17
    @52
    @44
    @49
    @45
    vy
    vx
    vt
    elequ1
    anbi1d
    rexbidv
    rspccv
    @31
    @50
    @36
    vt
    @17
    @31
    @43
    @17
    wcel
    #
    @50
    wa
    #
    wa
    @43
    @33
    wcel
    #
    @50
    @36
    @54
    @55
    @31
    @54
    @53
    @49
    wa
    #
    @55
    @53
    @49
    @56
    @45
    @56
    id
    adantrr
    @32
    @49
    vq
    @43
    @17
    vq
    vt
    vx
    elequ2
    elrab
    sylibr
    adantl
    @31
    @53
    @50
    simprr
    @9
    @50
    vp
    @43
    @33
    @6
    @43
    wceq
    @7
    @49
    @8
    @45
    vp
    vt
    vx
    elequ2
    @6
    @43
    @4
    sseq1
    anbi12d
    rspcev
    syl2anc
    rexlimdvaa
    syl9r
    sylbid
    ralrimiv
    @28
    @35
    @38
    wa
    vs
    @33
    @29
    @1
    @33
    wceq
    #
    @2
    @35
    @27
    @38
    @1
    @33
    com
    cdom
    breq1
    @57
    @11
    @37
    vo
    @19
    @57
    @10
    @36
    @5
    @9
    vp
    @1
    @33
    rexeq
    imbi2d
    ralbidv
    anbi12d
    rspcev
    syl12anc
    3expia
    @20
    @26
    @22
    @30
    @15
    @20
    @25
    @16
    @3
    @19
    cJ
    unieq
    eleq2d
    @20
    @28
    @13
    vs
    @29
    @14
    @19
    cJ
    pweq
    @20
    @27
    @12
    @2
    @11
    vo
    @19
    cJ
    raleq
    anbi2d
    rexeqbidv
    imbi12d
    syl5ibcom
    expimpd
    rexlimiv
    sylbi
    ralrimiv
    vx
    vs
    vo
    vp
    cJ
    @16
    @16
    eqid
    is1stc2
    sylanbrc
end
