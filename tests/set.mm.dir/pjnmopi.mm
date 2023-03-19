include "c0h.mm"
include "wne.mm"
include "cpjh.mm"
include "cfv.mm"
include "cnop.mm"
include "cv.mm"
include "cno.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "chil.mm"
include "wrex.mm"
include "cab.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wf.mm"
include "pjfi.mm"
include "nmopval.mm"
include "ax-mp.mm"
include "wral.mm"
include "wi.mm"
include "cr.mm"
include "wcel.mm"
include "vex.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "elab.mm"
include "cch.mm"
include "pjnorm.mm"
include "mpan.mm"
include "pjhcli.mm"
include "normcl.mm"
include "syl.mm"
include "1re.mm"
include "letr.mm"
include "mp3an3.mm"
include "syl2anc.mm"
include "mpand.mm"
include "imp.mm"
include "breq1.mm"
include "biimparc.mm"
include "sylan.mm"
include "expl.mm"
include "rexlimiv.mm"
include "sylbi.mm"
include "rgen.mm"
include "cheli.mm"
include "adantr.mm"
include "eqle.mm"
include "pjid.mm"
include "fveq2d.mm"
include "simpr.mm"
include "eqtr2d.mm"
include "jca32.mm"
include "reximi2.mm"
include "c0v.mm"
include "chne0i.mm"
include "chshii.mm"
include "norm1exi.mm"
include "bitri.mm"
include "1ex.mm"
include "3imtr4i.mm"
include "breq2.mm"
include "rspcev.mm"
include "ex.mm"
include "ralrimivw.mm"
include "wss.mm"
include "nmopsetretHIL.mm"
include "ressxr.mm"
include "sstri.mm"
include "rexri.mm"
include "supxr2.mm"
include "mpanl12.mm"
include "sylancr.mm"
include "syl5eq.mm"

theorem pjnmopi
  let cH: class H
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume pjhmop.1: |- H e. CH


  assert |- ( H =/= 0H -> ( normop ` ( projh ` H ) ) = 1 )

  proof
    cH
    c0h
    wne
    #
    cH
    cpjh
    cfv
    #
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
    @3
    @1
    cfv
    #
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
    chil
    chil
    @1
    wf
    #
    @2
    @13
    wceq
    cH
    pjhmop.1
    pjfi
    #
    vx
    vy
    @1
    nmopval
    ax-mp
    @0
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
    @16
    c1
    clt
    wbr
    #
    @16
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
    #
    @13
    c1
    wceq
    #
    @17
    vz
    @12
    @16
    @12
    wcel
    @5
    @16
    @8
    wceq
    #
    wa
    #
    vy
    chil
    wrex
    #
    @17
    @11
    @28
    vx
    @16
    vz
    vex
    @6
    @16
    wceq
    #
    @10
    @27
    vy
    chil
    @29
    @9
    @26
    @5
    @6
    @16
    @8
    eqeq1
    anbi2d
    rexbidv
    elab
    @27
    @17
    vy
    chil
    @3
    chil
    wcel
    #
    @5
    @26
    @17
    @30
    @5
    wa
    @8
    c1
    cle
    wbr
    #
    @26
    @17
    @30
    @5
    @31
    @30
    @8
    @4
    cle
    wbr
    #
    @5
    @31
    cH
    cch
    wcel
    #
    @30
    @32
    pjhmop.1
    @3
    cH
    pjnorm
    mpan
    @30
    @8
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    @32
    @5
    wa
    @31
    wi
    #
    @30
    @7
    chil
    wcel
    @34
    @3
    cH
    pjhmop.1
    pjhcli
    @7
    normcl
    syl
    @3
    normcl
    #
    @34
    @35
    c1
    cr
    wcel
    @36
    1re
    @8
    @4
    c1
    letr
    mp3an3
    syl2anc
    mpand
    imp
    @26
    @17
    @31
    @16
    @8
    c1
    cle
    breq1
    biimparc
    sylan
    expl
    rexlimiv
    sylbi
    rgen
    @0
    @23
    vz
    cr
    @0
    @19
    @22
    @0
    c1
    @12
    wcel
    #
    @19
    @22
    @4
    c1
    wceq
    #
    vy
    cH
    wrex
    #
    @5
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
    @0
    @38
    @39
    @42
    vy
    cH
    chil
    @3
    cH
    wcel
    #
    @39
    wa
    #
    @30
    @5
    @41
    @44
    @30
    @39
    @3
    cH
    pjhmop.1
    cheli
    #
    adantr
    @44
    @35
    @39
    @5
    @44
    @30
    @35
    @46
    @37
    syl
    @4
    c1
    eqle
    sylan
    @45
    @8
    @4
    c1
    @44
    @8
    @4
    wceq
    @39
    @44
    @7
    @3
    cno
    @33
    @44
    @7
    @3
    wceq
    pjhmop.1
    @3
    cH
    pjid
    mpan
    fveq2d
    adantr
    @44
    @39
    simpr
    eqtr2d
    jca32
    reximi2
    @0
    @3
    c0v
    wne
    vy
    cH
    wrex
    @40
    vy
    cH
    pjhmop.1
    chne0i
    vy
    vy
    cH
    cH
    pjhmop.1
    chshii
    norm1exi
    bitri
    @11
    @43
    vx
    c1
    1ex
    @6
    c1
    wceq
    #
    @10
    @42
    vy
    chil
    @47
    @9
    @41
    @5
    @6
    c1
    @8
    eqeq1
    anbi2d
    rexbidv
    elab
    3imtr4i
    @21
    @19
    vw
    c1
    @12
    @20
    c1
    @16
    clt
    breq2
    rspcev
    sylan
    ex
    ralrimivw
    @12
    cxr
    wss
    c1
    cxr
    wcel
    @18
    @24
    wa
    @25
    @12
    cr
    cxr
    @14
    @12
    cr
    wss
    @15
    vx
    vy
    @1
    nmopsetretHIL
    ax-mp
    ressxr
    sstri
    c1
    1re
    rexri
    vz
    vw
    @12
    c1
    supxr2
    mpanl12
    sylancr
    syl5eq
end
