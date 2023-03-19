include "chil.mm"
include "c0h.mm"
include "wne.mm"
include "cuo.mm"
include "wcel.mm"
include "wa.mm"
include "cnop.mm"
include "cfv.mm"
include "cv.mm"
include "cno.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wf.mm"
include "clo.mm"
include "unoplin.mm"
include "lnopf.mm"
include "syl.mm"
include "nmopval.mm"
include "adantl.mm"
include "wss.mm"
include "wral.mm"
include "wi.mm"
include "cr.mm"
include "nmopsetretHIL.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "1re.mm"
include "rexri.mm"
include "jctir.mm"
include "vex.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "elab.mm"
include "unopnorm.mm"
include "eqeq2d.mm"
include "breq1.mm"
include "biimparc.mm"
include "syl6bi.mm"
include "rexlimdva.mm"
include "imp.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "c0v.mm"
include "hne0.mm"
include "norm1hex.mm"
include "sylbb.mm"
include "adantr.mm"
include "1le1.mm"
include "mpbiri.mm"
include "a1i.mm"
include "wb.mm"
include "eqeq2.mm"
include "mpbid.mm"
include "eqcomd.mm"
include "ex.mm"
include "jcad.mm"
include "adantll.mm"
include "reximdva.mm"
include "mpd.mm"
include "1ex.mm"
include "sylibr.mm"
include "breq2.mm"
include "rspcev.mm"
include "sylan.mm"
include "supxr2.mm"
include "syl12anc.mm"
include "eqtrd.mm"

theorem nmopun
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( ~H =/= 0H /\ T e. UniOp ) -> ( normop ` T ) = 1 )

  proof
    chil
    c0h
    wne
    #
    cT
    cuo
    wcel
    #
    wa
    #
    cT
    cnop
    cfv
    #
    vy
    cv
    #
    cno
    cfv
    #
    c1
    cle
    wbr
    #
    vx
    cv
    #
    @4
    cT
    cfv
    cno
    cfv
    #
    wceq
    #
    wa
    #
    vy
    chil
    wrex
    #
    vx
    cab
    #
    cxr
    clt
    csup
    #
    c1
    @1
    @3
    @13
    wceq
    #
    @0
    @1
    chil
    chil
    cT
    wf
    #
    @14
    @1
    cT
    clo
    wcel
    @15
    cT
    unoplin
    cT
    lnopf
    syl
    #
    vx
    vy
    cT
    nmopval
    syl
    adantl
    @2
    @12
    cxr
    wss
    #
    c1
    cxr
    wcel
    #
    wa
    vz
    cv
    #
    c1
    cle
    wbr
    #
    vz
    @12
    wral
    #
    @19
    c1
    clt
    wbr
    #
    @19
    vw
    cv
    #
    clt
    wbr
    #
    vw
    @12
    wrex
    #
    wi
    #
    vz
    cr
    wral
    @13
    c1
    wceq
    @2
    @17
    @18
    @1
    @17
    @0
    @1
    @15
    @17
    @16
    @15
    @12
    cr
    cxr
    vx
    vy
    cT
    nmopsetretHIL
    ressxr
    syl6ss
    syl
    adantl
    c1
    1re
    rexri
    jctir
    @1
    @21
    @0
    @1
    @20
    vz
    @12
    @19
    @12
    wcel
    @1
    @6
    @19
    @8
    wceq
    #
    wa
    #
    vy
    chil
    wrex
    #
    @20
    @11
    @29
    vx
    @19
    vz
    vex
    @7
    @19
    wceq
    #
    @10
    @28
    vy
    chil
    @30
    @9
    @27
    @6
    @7
    @19
    @8
    eqeq1
    anbi2d
    rexbidv
    elab
    @1
    @29
    @20
    @1
    @28
    @20
    vy
    chil
    @1
    @4
    chil
    wcel
    #
    wa
    #
    @28
    @6
    @19
    @5
    wceq
    #
    wa
    @20
    @32
    @27
    @33
    @6
    @32
    @8
    @5
    @19
    @4
    cT
    unopnorm
    #
    eqeq2d
    anbi2d
    @33
    @20
    @6
    @19
    @5
    c1
    cle
    breq1
    biimparc
    syl6bi
    rexlimdva
    imp
    sylan2b
    ralrimiva
    adantl
    @2
    @26
    vz
    cr
    @2
    @19
    cr
    wcel
    #
    wa
    #
    @22
    @25
    @36
    c1
    @12
    wcel
    #
    @22
    @25
    @2
    @37
    @35
    @2
    @6
    c1
    @8
    wceq
    #
    wa
    #
    vy
    chil
    wrex
    #
    @37
    @2
    @5
    c1
    wceq
    #
    vy
    chil
    wrex
    #
    @40
    @0
    @42
    @1
    @0
    @4
    c0v
    wne
    vy
    chil
    wrex
    @42
    vy
    hne0
    vy
    vy
    norm1hex
    sylbb
    adantr
    @2
    @41
    @39
    vy
    chil
    @1
    @31
    @41
    @39
    wi
    @0
    @32
    @41
    @6
    @38
    @41
    @6
    wi
    @32
    @41
    @6
    c1
    c1
    cle
    wbr
    1le1
    @5
    c1
    c1
    cle
    breq1
    mpbiri
    a1i
    @32
    @41
    @38
    @32
    @41
    wa
    #
    @8
    c1
    @43
    @8
    @5
    wceq
    #
    @8
    c1
    wceq
    #
    @32
    @44
    @41
    @34
    adantr
    @41
    @44
    @45
    wb
    @32
    @5
    c1
    @8
    eqeq2
    adantl
    mpbid
    eqcomd
    ex
    jcad
    adantll
    reximdva
    mpd
    @11
    @40
    vx
    c1
    1ex
    @7
    c1
    wceq
    #
    @10
    @39
    vy
    chil
    @46
    @9
    @38
    @6
    @7
    c1
    @8
    eqeq1
    anbi2d
    rexbidv
    elab
    sylibr
    adantr
    @24
    @22
    vw
    c1
    @12
    @23
    c1
    @19
    clt
    breq2
    rspcev
    sylan
    ex
    ralrimiva
    vz
    vw
    @12
    c1
    supxr2
    syl12anc
    eqtrd
end
