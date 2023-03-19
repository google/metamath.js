include "crn.mm"
include "cch.mm"
include "wcel.mm"
include "csh.mm"
include "cn.mm"
include "cv.mm"
include "wf.mm"
include "chli.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "cho.mm"
include "clo.mm"
include "hmoplin.mm"
include "ax-mp.mm"
include "rnelshi.mm"
include "cfv.mm"
include "cmv.mm"
include "co.mm"
include "c0v.mm"
include "wceq.mm"
include "csn.mm"
include "cxp.mm"
include "cno.mm"
include "ccom.mm"
include "cmopn.mm"
include "chil.mm"
include "cxmt.mm"
include "cha.mm"
include "eqid.mm"
include "hilxmet.mm"
include "methaus.mm"
include "mp1i.mm"
include "cmpt.mm"
include "clm.mm"
include "cmap.mm"
include "cres.mm"
include "cva.mm"
include "csm.mm"
include "cop.mm"
include "hhims.mm"
include "hhlm.mm"
include "resss.mm"
include "eqsstri.mm"
include "ssbri.mm"
include "adantl.mm"
include "ctopon.mm"
include "mopntopon.mm"
include "ccn.mm"
include "lnopfi.mm"
include "a1i.mm"
include "feqmptd.mm"
include "ccop.mm"
include "cbo.mm"
include "hmopbdoptHIL.mm"
include "wb.mm"
include "lnopcnbd.mm"
include "mpbir.mm"
include "hhcno.mm"
include "eleqtri.mm"
include "syl6eqelr.mm"
include "cnmptid.mm"
include "cnv.mm"
include "ctx.mm"
include "hhnv.mm"
include "hhvs.mm"
include "vmcn.mm"
include "cnmpt12f.mm"
include "lmcn.mm"
include "wral.mm"
include "wss.mm"
include "simpl.mm"
include "shssii.mm"
include "fss.mm"
include "sylancl.mm"
include "ffvelrnda.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "wfn.mm"
include "ffn.mm"
include "eqeq12d.mm"
include "ralrn.mm"
include "fveq1i.mm"
include "hocoi.mm"
include "syl5reqr.mm"
include "mprgbir.mm"
include "ffvelrn.mm"
include "adantlr.mm"
include "rspccv.mm"
include "mpsyl.mm"
include "eqeltrd.mm"
include "hvsubeq0.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "eqtrd.mm"
include "fvco3.mm"
include "ax-hv0cl.mm"
include "elexi.mm"
include "fvconst2.mm"
include "3eqtr4d.mm"
include "ralrimiva.mm"
include "fnmpti.mm"
include "fnfco.mm"
include "sylancr.mm"
include "fconst.mm"
include "eqfnfv.mm"
include "vex.mm"
include "hlimveci.mm"
include "3brtr3d.mm"
include "c1.mm"
include "cz.mm"
include "1zzd.mm"
include "nnuz.mm"
include "lmconst.mm"
include "syl3anc.mm"
include "lmmo.mm"
include "ffvelrni.mm"
include "mpbid.mm"
include "fnfvelrn.mm"
include "eqeltrrd.mm"
include "gen2.mm"
include "isch2.mm"
include "mpbir2an.mm"

theorem hmopidmchi
  let cT: class T
  let vf: setvar f
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume hmopidmch.1: |- T e. HrmOp
  assume hmopidmch.2: |- ( T o. T ) = T


  assert |- ran T e. CH

  proof
    cT
    crn
    #
    cch
    wcel
    @0
    csh
    wcel
    cn
    @0
    vf
    cv
    #
    wf
    #
    @1
    vx
    cv
    #
    chli
    wbr
    #
    wa
    #
    @3
    @0
    wcel
    wi
    #
    vx
    wal
    vf
    wal
    cT
    cT
    cho
    wcel
    #
    cT
    clo
    wcel
    #
    hmopidmch.1
    cT
    hmoplin
    ax-mp
    #
    rnelshi
    #
    @6
    vf
    vx
    @5
    @3
    cT
    cfv
    #
    @3
    @0
    @5
    @11
    @3
    cmv
    co
    #
    c0v
    wceq
    #
    @11
    @3
    wceq
    #
    @5
    @12
    c0v
    cn
    c0v
    csn
    #
    cxp
    #
    cno
    cmv
    ccom
    #
    cmopn
    cfv
    #
    @17
    chil
    cxmt
    cfv
    wcel
    #
    @18
    cha
    wcel
    @5
    @17
    @17
    eqid
    #
    hilxmet
    #
    @17
    @18
    chil
    @18
    eqid
    #
    methaus
    mp1i
    @5
    vy
    chil
    vy
    cv
    #
    cT
    cfv
    #
    @23
    cmv
    co
    #
    cmpt
    #
    @1
    ccom
    #
    @3
    @26
    cfv
    #
    @16
    @12
    @18
    clm
    cfv
    #
    @5
    @3
    @1
    @26
    @18
    @18
    @4
    @1
    @3
    @29
    wbr
    @2
    chli
    @29
    @1
    @3
    chli
    @29
    chil
    cn
    cmap
    co
    #
    cres
    @29
    @17
    cva
    csm
    cop
    cno
    cop
    #
    @18
    @31
    eqid
    #
    @17
    @31
    @32
    @20
    hhims
    #
    @22
    hhlm
    @29
    @30
    resss
    eqsstri
    ssbri
    adantl
    @5
    vy
    @24
    @23
    cmv
    @18
    @18
    @18
    @18
    chil
    @19
    @18
    chil
    ctopon
    cfv
    wcel
    #
    @5
    @21
    @17
    @18
    chil
    @22
    mopntopon
    mp1i
    #
    @5
    vy
    chil
    @24
    cmpt
    cT
    @18
    @18
    ccn
    co
    #
    @5
    vy
    chil
    chil
    cT
    chil
    chil
    cT
    wf
    #
    @5
    cT
    @9
    lnopfi
    #
    a1i
    feqmptd
    cT
    ccop
    @36
    cT
    ccop
    wcel
    #
    cT
    cbo
    wcel
    #
    @7
    @40
    hmopidmch.1
    cT
    hmopbdoptHIL
    ax-mp
    @8
    @39
    @40
    wb
    @9
    cT
    lnopcnbd
    ax-mp
    mpbir
    @17
    @18
    @20
    @22
    hhcno
    eleqtri
    syl6eqelr
    @5
    vy
    @18
    chil
    @35
    cnmptid
    @31
    cnv
    wcel
    cmv
    @18
    @18
    ctx
    co
    @18
    ccn
    co
    wcel
    @5
    @31
    @32
    hhnv
    @17
    @31
    @18
    cmv
    @33
    @22
    @31
    @32
    hhvs
    vmcn
    mp1i
    cnmpt12f
    lmcn
    @5
    @27
    @16
    wceq
    #
    vk
    cv
    #
    @27
    cfv
    #
    @42
    @16
    cfv
    #
    wceq
    #
    vk
    cn
    wral
    #
    @5
    @45
    vk
    cn
    @5
    @42
    cn
    wcel
    #
    wa
    #
    @42
    @1
    cfv
    #
    @26
    cfv
    #
    c0v
    @43
    @44
    @48
    @50
    @49
    cT
    cfv
    #
    @49
    cmv
    co
    #
    c0v
    @48
    @49
    chil
    wcel
    #
    @50
    @52
    wceq
    @5
    cn
    chil
    @42
    @1
    @5
    @2
    @0
    chil
    wss
    cn
    chil
    @1
    wf
    #
    @2
    @4
    simpl
    @0
    @10
    shssii
    cn
    @0
    chil
    @1
    fss
    sylancl
    #
    ffvelrnda
    #
    vy
    @49
    @25
    @52
    chil
    @26
    @23
    @49
    wceq
    #
    @24
    @51
    @23
    @49
    cmv
    @23
    @49
    cT
    fveq2
    #
    @57
    id
    #
    oveq12d
    @26
    eqid
    #
    @51
    @49
    cmv
    ovex
    fvmpt
    syl
    @48
    @52
    c0v
    wceq
    #
    @51
    @49
    wceq
    #
    @24
    @23
    wceq
    #
    vy
    @0
    wral
    #
    @48
    @49
    @0
    wcel
    #
    @62
    @64
    @11
    cT
    cfv
    #
    @11
    wceq
    #
    vx
    chil
    cT
    chil
    wfn
    #
    @64
    @67
    vx
    chil
    wral
    wb
    @37
    @68
    @38
    chil
    chil
    cT
    ffn
    ax-mp
    #
    @63
    @67
    vy
    vx
    chil
    cT
    @23
    @11
    wceq
    #
    @24
    @66
    @23
    @11
    @23
    @11
    cT
    fveq2
    @70
    id
    eqeq12d
    ralrn
    ax-mp
    @3
    chil
    wcel
    #
    @11
    @3
    cT
    cT
    ccom
    #
    cfv
    @66
    @3
    @72
    cT
    hmopidmch.2
    fveq1i
    @3
    cT
    cT
    @38
    @38
    hocoi
    syl5reqr
    mprgbir
    @2
    @47
    @65
    @4
    cn
    @0
    @42
    @1
    ffvelrn
    adantlr
    @63
    @62
    vy
    @49
    @0
    @57
    @24
    @51
    @23
    @49
    @58
    @59
    eqeq12d
    rspccv
    mpsyl
    #
    @48
    @51
    chil
    wcel
    @53
    @61
    @62
    wb
    @48
    @51
    @49
    chil
    @73
    @56
    eqeltrd
    @56
    @51
    @49
    hvsubeq0
    syl2anc
    mpbird
    eqtrd
    @2
    @47
    @43
    @50
    wceq
    @4
    cn
    @0
    @42
    @26
    @1
    fvco3
    adantlr
    @47
    @44
    c0v
    wceq
    @5
    cn
    c0v
    @42
    c0v
    chil
    ax-hv0cl
    elexi
    #
    fvconst2
    adantl
    3eqtr4d
    ralrimiva
    @5
    @27
    cn
    wfn
    #
    @16
    cn
    wfn
    #
    @41
    @46
    wb
    @5
    @26
    chil
    wfn
    @54
    @75
    vy
    chil
    @25
    @26
    @24
    @23
    cmv
    ovex
    @60
    fnmpti
    @55
    chil
    cn
    @26
    @1
    fnfco
    sylancr
    cn
    @15
    @16
    wf
    @76
    cn
    c0v
    @74
    fconst
    cn
    @15
    @16
    ffn
    ax-mp
    vk
    cn
    @27
    @16
    eqfnfv
    sylancl
    mpbird
    @5
    @71
    @28
    @12
    wceq
    @4
    @71
    @2
    @3
    @1
    vx
    vex
    hlimveci
    adantl
    #
    vy
    @3
    @25
    @12
    chil
    @26
    @23
    @3
    wceq
    #
    @24
    @11
    @23
    @3
    cmv
    @23
    @3
    cT
    fveq2
    @78
    id
    oveq12d
    @60
    @11
    @3
    cmv
    ovex
    fvmpt
    syl
    3brtr3d
    @5
    @34
    c0v
    chil
    wcel
    #
    c1
    cz
    wcel
    @16
    c0v
    @29
    wbr
    @35
    @79
    @5
    ax-hv0cl
    a1i
    @5
    1zzd
    c0v
    @18
    c1
    chil
    cn
    nnuz
    lmconst
    syl3anc
    lmmo
    @5
    @11
    chil
    wcel
    #
    @71
    @13
    @14
    wb
    @5
    @71
    @80
    @77
    chil
    chil
    @3
    cT
    @38
    ffvelrni
    syl
    @77
    @11
    @3
    hvsubeq0
    syl2anc
    mpbid
    @5
    @68
    @71
    @11
    @0
    wcel
    @69
    @77
    chil
    @3
    cT
    fnfvelrn
    sylancr
    eqeltrrd
    gen2
    vx
    vf
    @0
    isch2
    mpbir2an
end
