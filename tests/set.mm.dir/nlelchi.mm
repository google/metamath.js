include "cnl.mm"
include "cfv.mm"
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
include "nlelshi.mm"
include "chil.mm"
include "cc0.mm"
include "wceq.mm"
include "vex.mm"
include "hlimveci.mm"
include "adantl.mm"
include "ccom.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cha.mm"
include "eqid.mm"
include "cnfldhaus.mm"
include "a1i.mm"
include "cno.mm"
include "cmv.mm"
include "cmopn.mm"
include "clm.mm"
include "cmap.mm"
include "co.mm"
include "cres.mm"
include "cva.mm"
include "csm.mm"
include "cop.mm"
include "hhims.mm"
include "hhlm.mm"
include "resss.mm"
include "eqsstri.mm"
include "ssbri.mm"
include "ccn.mm"
include "ccnfn.mm"
include "hhcnf.mm"
include "eleqtri.mm"
include "lmcn.mm"
include "csn.mm"
include "cxp.mm"
include "wral.mm"
include "cc.mm"
include "lnfnfi.mm"
include "ffvelrn.mm"
include "adantlr.mm"
include "elnlfn2.mm"
include "sylancr.mm"
include "fvco3.mm"
include "c0ex.mm"
include "fvconst2.mm"
include "3eqtr4d.mm"
include "ralrimiva.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "ax-mp.mm"
include "wss.mm"
include "simpl.mm"
include "shssii.mm"
include "fss.mm"
include "sylancl.mm"
include "fnfco.mm"
include "fconst.mm"
include "eqfnfv.mm"
include "mpbird.mm"
include "ctopon.mm"
include "c1.mm"
include "cz.mm"
include "cnfldtopon.mm"
include "0cnd.mm"
include "1zzd.mm"
include "nnuz.mm"
include "lmconst.mm"
include "syl3anc.mm"
include "eqbrtrd.mm"
include "lmmo.mm"
include "elnlfn.mm"
include "sylanbrc.mm"
include "gen2.mm"
include "isch2.mm"
include "mpbir2an.mm"

theorem nlelchi
  let cT: class T
  let vf: setvar f
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  assume nlelch.1: |- T e. LinFn
  assume nlelch.2: |- T e. ContFn


  assert |- ( null ` T ) e. CH

  proof
    cT
    cnl
    cfv
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
    #
    wi
    #
    vx
    wal
    vf
    wal
    cT
    nlelch.1
    nlelshi
    #
    @7
    vf
    vx
    @5
    @3
    chil
    wcel
    #
    @3
    cT
    cfv
    #
    cc0
    wceq
    #
    @6
    @4
    @9
    @2
    @3
    @1
    vx
    vex
    hlimveci
    adantl
    @5
    @10
    cc0
    cT
    @1
    ccom
    #
    ccnfld
    ctopn
    cfv
    #
    @13
    cha
    wcel
    @5
    @13
    @13
    eqid
    #
    cnfldhaus
    a1i
    @5
    @3
    @1
    cT
    cno
    cmv
    ccom
    #
    cmopn
    cfv
    #
    @13
    @4
    @1
    @3
    @16
    clm
    cfv
    #
    wbr
    @2
    chli
    @17
    @1
    @3
    chli
    @17
    chil
    cn
    cmap
    co
    #
    cres
    @17
    @15
    cva
    csm
    cop
    cno
    cop
    #
    @16
    @19
    eqid
    #
    @15
    @19
    @20
    @15
    eqid
    #
    hhims
    @16
    eqid
    #
    hhlm
    @17
    @18
    resss
    eqsstri
    ssbri
    adantl
    cT
    @16
    @13
    ccn
    co
    #
    wcel
    @5
    cT
    ccnfn
    @23
    nlelch.2
    @15
    @16
    @13
    @21
    @22
    @14
    hhcnf
    eleqtri
    a1i
    lmcn
    @5
    @12
    cn
    cc0
    csn
    #
    cxp
    #
    cc0
    @13
    clm
    cfv
    #
    @5
    @12
    @25
    wceq
    #
    vn
    cv
    #
    @12
    cfv
    #
    @28
    @25
    cfv
    #
    wceq
    #
    vn
    cn
    wral
    #
    @5
    @31
    vn
    cn
    @5
    @28
    cn
    wcel
    #
    wa
    #
    @28
    @1
    cfv
    #
    cT
    cfv
    #
    cc0
    @29
    @30
    @34
    chil
    cc
    cT
    wf
    #
    @35
    @0
    wcel
    #
    @36
    cc0
    wceq
    cT
    nlelch.1
    lnfnfi
    #
    @2
    @33
    @38
    @4
    cn
    @0
    @28
    @1
    ffvelrn
    adantlr
    @35
    cT
    elnlfn2
    sylancr
    @2
    @33
    @29
    @36
    wceq
    @4
    cn
    @0
    @28
    cT
    @1
    fvco3
    adantlr
    @33
    @30
    cc0
    wceq
    @5
    cn
    cc0
    @28
    c0ex
    fvconst2
    adantl
    3eqtr4d
    ralrimiva
    @5
    @12
    cn
    wfn
    #
    @25
    cn
    wfn
    #
    @27
    @32
    wb
    @5
    cT
    chil
    wfn
    #
    cn
    chil
    @1
    wf
    #
    @40
    @37
    @42
    @39
    chil
    cc
    cT
    ffn
    ax-mp
    @5
    @2
    @0
    chil
    wss
    @43
    @2
    @4
    simpl
    @0
    @8
    shssii
    cn
    @0
    chil
    @1
    fss
    sylancl
    chil
    cn
    cT
    @1
    fnfco
    sylancr
    cn
    @24
    @25
    wf
    @41
    cn
    cc0
    c0ex
    fconst
    cn
    @24
    @25
    ffn
    ax-mp
    vn
    cn
    @12
    @25
    eqfnfv
    sylancl
    mpbird
    @5
    @13
    cc
    ctopon
    cfv
    wcel
    #
    cc0
    cc
    wcel
    c1
    cz
    wcel
    @25
    cc0
    @26
    wbr
    @44
    @5
    @13
    @14
    cnfldtopon
    a1i
    @5
    0cnd
    @5
    1zzd
    cc0
    @13
    c1
    cc
    cn
    nnuz
    lmconst
    syl3anc
    eqbrtrd
    lmmo
    @37
    @6
    @9
    @11
    wa
    wb
    @39
    @3
    cT
    elnlfn
    ax-mp
    sylanbrc
    gen2
    vx
    vf
    @0
    isch2
    mpbir2an
end
