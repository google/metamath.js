include "chli.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "cn.mm"
include "csn.mm"
include "cxp.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cha.mm"
include "wcel.mm"
include "eqid.mm"
include "cnfldhaus.mm"
include "a1i.mm"
include "chil.mm"
include "cv.mm"
include "cmpt.mm"
include "ccom.mm"
include "clm.mm"
include "cno.mm"
include "cmv.mm"
include "cmopn.mm"
include "wbr.mm"
include "cdm.mm"
include "ccau.mm"
include "wrex.mm"
include "ax-hcompl.mm"
include "wfn.mm"
include "wf.mm"
include "hlimf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "fnbr.mm"
include "mpan.mm"
include "rexlimivw.mm"
include "3syl.mm"
include "wfun.mm"
include "wb.mm"
include "ffun.mm"
include "funfvbrb.mm"
include "mp2b.mm"
include "sylib.mm"
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
include "syl.mm"
include "cxmt.mm"
include "ctopon.mm"
include "hilxmet.mm"
include "mopntopon.mm"
include "mp1i.mm"
include "cnmptid.mm"
include "sseldd.mm"
include "cnmptc.mm"
include "cnv.mm"
include "ctx.mm"
include "ccn.mm"
include "hhnv.mm"
include "hhip.mm"
include "dipcn.mm"
include "cnmpt12f.mm"
include "lmcn.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "cort.mm"
include "ffvelrnda.mm"
include "wss.mm"
include "ocel.mm"
include "adantr.mm"
include "mpbid.mm"
include "simpld.mm"
include "oveq1.mm"
include "ovex.mm"
include "fvmpt.mm"
include "simprd.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "eqtrd.mm"
include "ocss.mm"
include "fssd.mm"
include "fvco3.mm"
include "sylan.mm"
include "c0ex.mm"
include "fvconst2.mm"
include "adantl.mm"
include "3eqtr4d.mm"
include "ralrimiva.mm"
include "fnmpti.mm"
include "fnfco.mm"
include "sylancr.mm"
include "fconst.mm"
include "eqfnfv.mm"
include "sylancl.mm"
include "mpbird.mm"
include "fvex.mm"
include "hlimveci.mm"
include "3brtr3d.mm"
include "cc.mm"
include "c1.mm"
include "cz.mm"
include "cnfldtopon.mm"
include "0cnd.mm"
include "1zzd.mm"
include "nnuz.mm"
include "lmconst.mm"
include "syl3anc.mm"
include "lmmo.mm"

theorem occllem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  let vx: setvar x
  assume occl.1: |- ( ph -> A C_ ~H )
  assume occl.2: |- ( ph -> F e. Cauchy )
  assume occl.3: |- ( ph -> F : NN --> ( _|_ ` A ) )
  assume occl.4: |- ( ph -> B e. A )


  assert |- ( ph -> ( ( ~~>v ` F ) .ih B ) = 0 )

  proof
    wph
    cF
    chli
    cfv
    #
    cB
    csp
    co
    #
    cc0
    cn
    cc0
    csn
    #
    cxp
    #
    ccnfld
    ctopn
    cfv
    #
    @4
    cha
    wcel
    wph
    @4
    @4
    eqid
    #
    cnfldhaus
    a1i
    wph
    vx
    chil
    vx
    cv
    #
    cB
    csp
    co
    #
    cmpt
    #
    cF
    ccom
    #
    @0
    @8
    cfv
    #
    @3
    @1
    @4
    clm
    cfv
    #
    wph
    @0
    cF
    @8
    cno
    cmv
    ccom
    #
    cmopn
    cfv
    #
    @4
    wph
    cF
    @0
    chli
    wbr
    #
    cF
    @0
    @13
    clm
    cfv
    #
    wbr
    wph
    cF
    chli
    cdm
    #
    wcel
    #
    @14
    wph
    cF
    ccau
    wcel
    cF
    @6
    chli
    wbr
    #
    vx
    chil
    wrex
    @17
    occl.2
    vx
    cF
    ax-hcompl
    @18
    @17
    vx
    chil
    chli
    @16
    wfn
    #
    @18
    @17
    @16
    chil
    chli
    wf
    #
    @19
    hlimf
    @16
    chil
    chli
    ffn
    ax-mp
    @16
    cF
    @6
    chli
    fnbr
    mpan
    rexlimivw
    3syl
    @20
    chli
    wfun
    @17
    @14
    wb
    hlimf
    @16
    chil
    chli
    ffun
    cF
    chli
    funfvbrb
    mp2b
    sylib
    #
    chli
    @15
    cF
    @0
    chli
    @15
    chil
    cn
    cmap
    co
    #
    cres
    @15
    @12
    cva
    csm
    cop
    cno
    cop
    #
    @13
    @23
    eqid
    #
    @12
    @23
    @24
    @12
    eqid
    #
    hhims
    #
    @13
    eqid
    #
    hhlm
    @15
    @22
    resss
    eqsstri
    ssbri
    syl
    wph
    vx
    @6
    cB
    csp
    @13
    @13
    @13
    @4
    chil
    @12
    chil
    cxmt
    cfv
    wcel
    @13
    chil
    ctopon
    cfv
    wcel
    wph
    @12
    @25
    hilxmet
    @12
    @13
    chil
    @27
    mopntopon
    mp1i
    #
    wph
    vx
    @13
    chil
    @28
    cnmptid
    wph
    vx
    cB
    @13
    @13
    chil
    chil
    @28
    @28
    wph
    cA
    chil
    cB
    occl.1
    occl.4
    sseldd
    cnmptc
    @23
    cnv
    wcel
    csp
    @13
    @13
    ctx
    co
    @4
    ccn
    co
    wcel
    wph
    @23
    @24
    hhnv
    @12
    csp
    @23
    @13
    @4
    @23
    @24
    hhip
    @26
    @27
    @5
    dipcn
    mp1i
    cnmpt12f
    lmcn
    wph
    @9
    @3
    wceq
    #
    vk
    cv
    #
    @9
    cfv
    #
    @30
    @3
    cfv
    #
    wceq
    #
    vk
    cn
    wral
    #
    wph
    @33
    vk
    cn
    wph
    @30
    cn
    wcel
    #
    wa
    #
    @30
    cF
    cfv
    #
    @8
    cfv
    #
    cc0
    @31
    @32
    @36
    @38
    @37
    cB
    csp
    co
    #
    cc0
    @36
    @37
    chil
    wcel
    #
    @38
    @39
    wceq
    @36
    @40
    @37
    @6
    csp
    co
    #
    cc0
    wceq
    #
    vx
    cA
    wral
    #
    @36
    @37
    cA
    cort
    cfv
    #
    wcel
    #
    @40
    @43
    wa
    #
    wph
    cn
    @44
    @30
    cF
    occl.3
    ffvelrnda
    wph
    @45
    @46
    wb
    #
    @35
    wph
    cA
    chil
    wss
    #
    @47
    occl.1
    vx
    @37
    cA
    ocel
    syl
    adantr
    mpbid
    #
    simpld
    vx
    @37
    @7
    @39
    chil
    @8
    @6
    @37
    cB
    csp
    oveq1
    @8
    eqid
    #
    @37
    cB
    csp
    ovex
    fvmpt
    syl
    @36
    cB
    cA
    wcel
    #
    @43
    @39
    cc0
    wceq
    #
    wph
    @51
    @35
    occl.4
    adantr
    @36
    @40
    @43
    @49
    simprd
    @42
    @52
    vx
    cB
    cA
    @6
    cB
    wceq
    @41
    @39
    cc0
    @6
    cB
    @37
    csp
    oveq2
    eqeq1d
    rspcv
    sylc
    eqtrd
    wph
    cn
    chil
    cF
    wf
    #
    @35
    @31
    @38
    wceq
    wph
    cn
    @44
    chil
    cF
    occl.3
    wph
    @48
    @44
    chil
    wss
    occl.1
    cA
    ocss
    syl
    fssd
    #
    cn
    chil
    @30
    @8
    cF
    fvco3
    sylan
    @35
    @32
    cc0
    wceq
    wph
    cn
    cc0
    @30
    c0ex
    fvconst2
    adantl
    3eqtr4d
    ralrimiva
    wph
    @9
    cn
    wfn
    #
    @3
    cn
    wfn
    #
    @29
    @34
    wb
    wph
    @8
    chil
    wfn
    @53
    @55
    vx
    chil
    @7
    @8
    @6
    cB
    csp
    ovex
    @50
    fnmpti
    @54
    chil
    cn
    @8
    cF
    fnfco
    sylancr
    cn
    @2
    @3
    wf
    @56
    cn
    cc0
    c0ex
    fconst
    cn
    @2
    @3
    ffn
    ax-mp
    vk
    cn
    @9
    @3
    eqfnfv
    sylancl
    mpbird
    wph
    @14
    @0
    chil
    wcel
    @10
    @1
    wceq
    @21
    @0
    cF
    cF
    chli
    fvex
    hlimveci
    vx
    @0
    @7
    @1
    chil
    @8
    @6
    @0
    cB
    csp
    oveq1
    @50
    @0
    cB
    csp
    ovex
    fvmpt
    3syl
    3brtr3d
    wph
    @4
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
    @3
    cc0
    @11
    wbr
    @57
    wph
    @4
    @5
    cnfldtopon
    a1i
    wph
    0cnd
    wph
    1zzd
    cc0
    @4
    c1
    cc
    cn
    nnuz
    lmconst
    syl3anc
    lmmo
end
