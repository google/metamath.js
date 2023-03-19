include "ccom.mm"
include "cdm.mm"
include "wcel.mm"
include "csn.mm"
include "cres.mm"
include "wfun.mm"
include "wa.mm"
include "wfn.mm"
include "cfv.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wral.mm"
include "relres.mm"
include "a1i.mm"
include "wi.mm"
include "dmfco.mm"
include "biimpd.mm"
include "funfni.mm"
include "wceq.mm"
include "dmressnsn.mm"
include "eleq2.mm"
include "velsn.mm"
include "dffun7.mm"
include "snidg.mm"
include "adantl.mm"
include "wb.mm"
include "eqcoms.mm"
include "adantr.mm"
include "mpbid.mm"
include "wal.mm"
include "wex.mm"
include "fvex.mm"
include "isseti.mm"
include "eqcom.mm"
include "fnbrfvb.mm"
include "syl5bb.mm"
include "breq1.mm"
include "biimpcd.mm"
include "anim12ii.mm"
include "eximdv.mm"
include "mpi.mm"
include "cvv.mm"
include "simpr.mm"
include "vex.mm"
include "brcog.mm"
include "sylancl.mm"
include "mpbird.mm"
include "biantrud.mm"
include "brres.mm"
include "syl6rbbr.mm"
include "ad2antlr.mm"
include "ex.mm"
include "sylibd.mm"
include "alrimiv.mm"
include "moim.mm"
include "syl.mm"
include "com23.mm"
include "rspcimdv.mm"
include "com13.mm"
include "sylbi.mm"
include "mpcom.mm"
include "imp31.mm"
include "snid.mm"
include "biantru.mm"
include "mobidv.mm"
include "syl6rbb.mm"
include "syl6bi.mm"
include "syl6com.mm"
include "a1d.mm"
include "pm2.43i.mm"
include "ralrimiv.mm"
include "sylanbrc.mm"

theorem funressnfv
  let cA: class A
  let cF: class F
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k


  assert |- ( ( ( X e. dom ( F o. G ) /\ Fun ( ( F o. G ) |` { X } ) ) /\ ( G Fn A /\ X e. A ) ) -> Fun ( F |` { ( G ` X ) } ) )

  proof
    cX
    cF
    cG
    ccom
    #
    cdm
    #
    wcel
    #
    @0
    cX
    csn
    #
    cres
    #
    wfun
    #
    wa
    cG
    cA
    wfn
    #
    cX
    cA
    wcel
    #
    wa
    #
    wa
    #
    cF
    cX
    cG
    cfv
    #
    csn
    #
    cres
    #
    wrel
    #
    vx
    cv
    #
    vy
    cv
    #
    @12
    wbr
    #
    vy
    wmo
    #
    vx
    @12
    cdm
    #
    wral
    @12
    wfun
    @13
    @9
    cF
    @11
    relres
    a1i
    @9
    @17
    vx
    @18
    @9
    @14
    @18
    wcel
    #
    @17
    wi
    #
    @2
    @5
    @8
    @9
    @20
    wi
    #
    @2
    @8
    @21
    wi
    @5
    @8
    @2
    @10
    cF
    cdm
    wcel
    #
    @21
    @2
    @22
    wi
    cA
    cX
    cG
    cG
    wfun
    cX
    cG
    cdm
    wcel
    wa
    @2
    @22
    cX
    cF
    cG
    dmfco
    biimpd
    funfni
    @22
    @18
    @11
    wceq
    #
    @21
    @10
    cF
    dmressnsn
    @23
    @19
    @9
    @17
    @23
    @19
    @14
    @11
    wcel
    #
    @9
    @17
    wi
    #
    @18
    @11
    @14
    eleq2
    @24
    @14
    @10
    wceq
    #
    @25
    vx
    @10
    velsn
    @26
    @9
    @17
    @26
    @9
    wa
    #
    @10
    @15
    cF
    wbr
    #
    @10
    @11
    wcel
    #
    wa
    #
    vy
    wmo
    #
    @17
    @9
    @31
    @26
    @9
    @28
    vy
    wmo
    #
    @31
    @2
    @5
    @8
    @32
    @4
    cdm
    #
    @3
    wceq
    #
    @2
    @5
    @8
    @32
    wi
    #
    wi
    cX
    @0
    dmressnsn
    @5
    @2
    @34
    @35
    @5
    @4
    wrel
    #
    @14
    @15
    @4
    wbr
    #
    vy
    wmo
    #
    vx
    @33
    wral
    #
    wa
    @2
    @34
    @35
    wi
    wi
    #
    vx
    vy
    @4
    dffun7
    @39
    @40
    @36
    @34
    @2
    @39
    @35
    @34
    @2
    @39
    @35
    wi
    @34
    @2
    wa
    #
    @38
    @35
    vx
    cX
    @33
    @41
    cX
    @3
    wcel
    #
    cX
    @33
    wcel
    #
    @2
    @42
    @34
    cX
    @1
    snidg
    adantl
    @34
    @42
    @43
    wb
    #
    @2
    @44
    @3
    @33
    @3
    @33
    cX
    eleq2
    eqcoms
    adantr
    mpbid
    @41
    @14
    cX
    wceq
    #
    wa
    #
    @8
    @38
    @32
    @46
    @8
    @38
    @32
    wi
    #
    @46
    @8
    wa
    #
    @28
    @37
    wi
    #
    vy
    wal
    @47
    @48
    @49
    vy
    @48
    @28
    cX
    @15
    @4
    wbr
    #
    @37
    @8
    @28
    @50
    wi
    @46
    @8
    @28
    @50
    @8
    @28
    wa
    #
    @50
    cX
    @15
    @0
    wbr
    #
    @51
    @52
    cX
    vz
    cv
    #
    cG
    wbr
    #
    @53
    @15
    cF
    wbr
    #
    wa
    #
    vz
    wex
    #
    @51
    @53
    @10
    wceq
    #
    vz
    wex
    @57
    vz
    @10
    cX
    cG
    fvex
    #
    isseti
    @51
    @58
    @56
    vz
    @8
    @58
    @54
    @28
    @55
    @8
    @58
    @54
    @58
    @10
    @53
    wceq
    @8
    @54
    @53
    @10
    eqcom
    cA
    cX
    @53
    cG
    fnbrfvb
    syl5bb
    biimpd
    @58
    @28
    @55
    @28
    @55
    wb
    @10
    @53
    @10
    @53
    @15
    cF
    breq1
    eqcoms
    biimpcd
    anim12ii
    eximdv
    mpi
    @8
    @52
    @57
    wb
    #
    @28
    @8
    @7
    @15
    cvv
    wcel
    @60
    @6
    @7
    simpr
    vy
    vex
    #
    vz
    cX
    @15
    cF
    cG
    cA
    cvv
    brcog
    sylancl
    adantr
    mpbird
    @7
    @50
    @52
    wb
    @6
    @28
    @7
    @52
    @52
    @42
    wa
    @50
    @7
    @42
    @52
    cX
    cA
    snidg
    biantrud
    cX
    @15
    @0
    @3
    @61
    brres
    syl6rbbr
    ad2antlr
    mpbird
    ex
    adantl
    @45
    @50
    @37
    wb
    #
    @41
    @8
    @62
    cX
    @14
    cX
    @14
    @15
    @4
    breq1
    eqcoms
    ad2antlr
    sylibd
    alrimiv
    @28
    @37
    vy
    moim
    syl
    ex
    com23
    rspcimdv
    ex
    com13
    adantl
    sylbi
    com13
    mpcom
    imp31
    @9
    @28
    @30
    vy
    @28
    @30
    wb
    @9
    @29
    @28
    @10
    @59
    snid
    biantru
    a1i
    mobidv
    mpbid
    adantl
    @27
    @30
    @16
    vy
    @26
    @30
    @16
    wb
    @9
    @26
    @16
    @10
    @15
    @12
    wbr
    @30
    @14
    @10
    @15
    @12
    breq1
    @10
    @15
    cF
    @11
    @61
    brres
    syl6rbb
    adantr
    mobidv
    mpbid
    ex
    sylbi
    syl6bi
    com23
    syl
    syl6com
    a1d
    imp31
    pm2.43i
    ralrimiv
    vx
    vy
    @12
    dffun7
    sylanbrc
end
