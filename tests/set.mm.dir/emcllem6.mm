include "cem.mm"
include "cli.mm"
include "wbr.mm"
include "wtru.mm"
include "cc0.mm"
include "caddc.mm"
include "co.mm"
include "c1.mm"
include "cvv.mm"
include "cn.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cseq.mm"
include "cv.mm"
include "cdiv.mm"
include "clog.mm"
include "cfv.mm"
include "cmin.mm"
include "csu.mm"
include "wcel.mm"
include "wceq.mm"
include "weq.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "wa.mm"
include "cr.mm"
include "nnrecre.mm"
include "crp.mm"
include "1rp.mm"
include "nnrp.mm"
include "rpreccld.mm"
include "rpaddcl.mm"
include "sylancr.mm"
include "relogcld.mm"
include "resubcld.mm"
include "recnd.mm"
include "crn.mm"
include "clt.mm"
include "csup.mm"
include "cdm.mm"
include "emcllem5.mm"
include "wf.mm"
include "emcllem1.mm"
include "simpri.mm"
include "a1i.mm"
include "cle.mm"
include "emcllem2.mm"
include "simprd.mm"
include "wral.mm"
include "wrex.mm"
include "1nn.mm"
include "simpli.mm"
include "ffvelrni.mm"
include "ax-mp.mm"
include "fvex.mm"
include "emcllem3.mm"
include "eqtr3d.mm"
include "1re.mm"
include "readdcl.mm"
include "ltaddrp.mm"
include "rplogcld.mm"
include "eqeltrrd.mm"
include "rpge0d.mm"
include "subge0d.mm"
include "mpbid.mm"
include "fveq2.mm"
include "breq1d.mm"
include "leidi.mm"
include "simpld.mm"
include "wi.mm"
include "peano2nn.mm"
include "syl.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "nnind.mm"
include "letrd.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "climsup.mm"
include "syl5eqbrr.mm"
include "climrel.mm"
include "releldmi.mm"
include "isumclim2.mm"
include "df-em.mm"
include "3brtr4g.mm"
include "cfz.mm"
include "cmpt.mm"
include "nnex.mm"
include "mptex.mm"
include "eqeltri.mm"
include "emcllem4.mm"
include "eqeltrd.mm"
include "pncan3d.mm"
include "eqtr2d.mm"
include "climadd.mm"
include "cc.mm"
include "trud.mm"
include "climcl.mm"
include "addid1i.mm"
include "syl6breq.mm"
include "pm3.2i.mm"

theorem emcllem6
  let cT: class T
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let vi: setvar i
  let vk: setvar k
  let vx: setvar x
  let cN: class N
  assume emcl.1: |- F = ( n e. NN |-> ( sum_ m e. ( 1 ... n ) ( 1 / m ) - ( log ` n ) ) )
  assume emcl.2: |- G = ( n e. NN |-> ( sum_ m e. ( 1 ... n ) ( 1 / m ) - ( log ` ( n + 1 ) ) ) )
  assume emcl.3: |- H = ( n e. NN |-> ( log ` ( 1 + ( 1 / n ) ) ) )
  assume emcl.4: |- T = ( n e. NN |-> ( ( 1 / n ) - ( log ` ( 1 + ( 1 / n ) ) ) ) )

  disjoint H m
  disjoint m n
  disjoint T m
  disjoint T n
  disjoint i k
  disjoint i x
  disjoint F i
  disjoint k x
  disjoint F k
  disjoint F x
  disjoint G i
  disjoint G k
  disjoint G x
  disjoint k m
  disjoint H k
  disjoint N m
  disjoint N n
  disjoint k n
  disjoint T k
  disjoint m x
  disjoint n x
  disjoint T x
  assert |- ( F ~~> gamma /\ G ~~> gamma )

  proof
    cF
    cem
    cli
    wbr
    #
    cG
    cem
    cli
    wbr
    #
    @0
    wtru
    cF
    cem
    cc0
    caddc
    co
    cem
    cli
    wtru
    cem
    cc0
    vk
    cG
    cH
    cF
    c1
    cvv
    cn
    nnuz
    wtru
    1zzd
    #
    wtru
    caddc
    cT
    c1
    cseq
    #
    cn
    c1
    vk
    cv
    #
    cdiv
    co
    #
    c1
    @5
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    vk
    csu
    cG
    cem
    cli
    wtru
    @8
    vk
    cT
    c1
    cn
    nnuz
    @2
    @4
    cn
    wcel
    #
    @4
    cT
    cfv
    @8
    wceq
    wtru
    vn
    @4
    c1
    vn
    cv
    #
    cdiv
    co
    #
    c1
    @11
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    @8
    cn
    cT
    vn
    vk
    weq
    #
    @11
    @5
    @13
    @7
    cmin
    @10
    @4
    c1
    cdiv
    oveq2
    #
    @14
    @12
    @6
    clog
    @14
    @11
    @5
    c1
    caddc
    @15
    oveq2d
    fveq2d
    #
    oveq12d
    emcl.4
    @5
    @7
    cmin
    ovex
    fvmpt
    adantl
    wtru
    @9
    wa
    #
    @8
    @17
    @5
    @7
    @9
    @5
    cr
    wcel
    #
    wtru
    @4
    nnrecre
    adantl
    #
    @17
    @6
    @17
    c1
    crp
    wcel
    @5
    crp
    wcel
    #
    @6
    crp
    wcel
    1rp
    @9
    @20
    wtru
    @9
    @4
    @4
    nnrp
    rpreccld
    adantl
    #
    c1
    @5
    rpaddcl
    sylancr
    relogcld
    resubcld
    recnd
    wtru
    @3
    cG
    crn
    cr
    clt
    csup
    #
    cli
    wbr
    @3
    cli
    cdm
    wcel
    wtru
    @3
    cG
    @22
    cli
    cT
    vm
    vn
    cF
    cG
    cH
    emcl.1
    emcl.2
    emcl.3
    emcl.4
    emcllem5
    #
    wtru
    vx
    vk
    cG
    c1
    cn
    nnuz
    @2
    cn
    cr
    cG
    wf
    #
    wtru
    cn
    cr
    cF
    wf
    #
    @24
    vm
    vn
    cF
    cG
    emcl.1
    emcl.2
    emcllem1
    #
    simpri
    #
    a1i
    @9
    @4
    cG
    cfv
    #
    @4
    c1
    caddc
    co
    #
    cG
    cfv
    cle
    wbr
    #
    wtru
    @9
    @29
    cF
    cfv
    #
    @4
    cF
    cfv
    #
    cle
    wbr
    #
    @30
    vm
    vn
    cF
    cG
    @4
    emcl.1
    emcl.2
    emcllem2
    #
    simprd
    adantl
    wtru
    c1
    cF
    cfv
    #
    cr
    wcel
    #
    @28
    @35
    cle
    wbr
    #
    vk
    cn
    wral
    #
    @28
    vx
    cv
    #
    cle
    wbr
    #
    vk
    cn
    wral
    #
    vx
    cr
    wrex
    c1
    cn
    wcel
    @36
    1nn
    cn
    cr
    c1
    cF
    @25
    @24
    @26
    simpli
    #
    ffvelrni
    ax-mp
    #
    wtru
    @37
    vk
    cn
    @17
    @28
    @32
    @35
    @9
    @28
    cr
    wcel
    wtru
    cn
    cr
    @4
    cG
    @27
    ffvelrni
    adantl
    #
    @9
    @32
    cr
    wcel
    #
    wtru
    cn
    cr
    @4
    cF
    @42
    ffvelrni
    #
    adantl
    #
    @36
    @17
    @43
    a1i
    @17
    cc0
    @32
    @28
    cmin
    co
    #
    cle
    wbr
    @28
    @32
    cle
    wbr
    @17
    @48
    @17
    @7
    @48
    crp
    @17
    @4
    cH
    cfv
    #
    @7
    @48
    @9
    @49
    @7
    wceq
    wtru
    vn
    @4
    @13
    @7
    cn
    cH
    @16
    emcl.3
    @6
    clog
    fvex
    fvmpt
    adantl
    @9
    @49
    @48
    wceq
    wtru
    vm
    vn
    cF
    cG
    cH
    @4
    emcl.1
    emcl.2
    emcl.3
    emcllem3
    adantl
    #
    eqtr3d
    @17
    @6
    @17
    c1
    cr
    wcel
    #
    @18
    @6
    cr
    wcel
    1re
    @19
    c1
    @5
    readdcl
    sylancr
    @17
    @51
    @20
    c1
    @6
    clt
    wbr
    1re
    @21
    c1
    @5
    ltaddrp
    sylancr
    rplogcld
    eqeltrrd
    rpge0d
    @17
    @32
    @28
    @47
    @44
    subge0d
    mpbid
    @9
    @32
    @35
    cle
    wbr
    #
    wtru
    @39
    cF
    cfv
    #
    @35
    cle
    wbr
    @35
    @35
    cle
    wbr
    @52
    @31
    @35
    cle
    wbr
    #
    @52
    vx
    vk
    @4
    @39
    c1
    wceq
    @53
    @35
    @35
    cle
    @39
    c1
    cF
    fveq2
    breq1d
    vx
    vk
    weq
    @53
    @32
    @35
    cle
    @39
    @4
    cF
    fveq2
    breq1d
    #
    @39
    @29
    wceq
    @53
    @31
    @35
    cle
    @39
    @29
    cF
    fveq2
    breq1d
    @55
    @35
    @43
    leidi
    @9
    @33
    @52
    @54
    @9
    @33
    @30
    @34
    simpld
    @9
    @31
    cr
    wcel
    #
    @45
    @36
    @33
    @52
    wa
    @54
    wi
    @9
    @29
    cn
    wcel
    @56
    @4
    peano2nn
    cn
    cr
    @29
    cF
    @42
    ffvelrni
    syl
    @46
    @36
    @9
    @43
    a1i
    @31
    @32
    @35
    letr
    syl3anc
    mpand
    nnind
    adantl
    letrd
    ralrimiva
    @41
    @38
    vx
    @35
    cr
    @39
    @35
    wceq
    @40
    @37
    vk
    cn
    @39
    @35
    @28
    cle
    breq2
    ralbidv
    rspcev
    sylancr
    climsup
    syl5eqbrr
    @3
    @22
    cli
    climrel
    releldmi
    syl
    isumclim2
    @23
    vk
    df-em
    3brtr4g
    #
    cF
    cvv
    wcel
    wtru
    cF
    vn
    cn
    c1
    @10
    cfz
    co
    c1
    vm
    cv
    cdiv
    co
    vm
    csu
    @10
    clog
    cfv
    cmin
    co
    #
    cmpt
    cvv
    emcl.1
    vn
    cn
    @58
    nnex
    mptex
    eqeltri
    a1i
    cH
    cc0
    cli
    wbr
    wtru
    vm
    vn
    cF
    cG
    cH
    emcl.1
    emcl.2
    emcl.3
    emcllem4
    a1i
    @17
    @28
    @44
    recnd
    #
    @17
    @49
    @17
    @49
    @48
    cr
    @50
    @17
    @32
    @28
    @47
    @44
    resubcld
    eqeltrd
    recnd
    @17
    @28
    @49
    caddc
    co
    @28
    @48
    caddc
    co
    @32
    @17
    @49
    @48
    @28
    caddc
    @50
    oveq2d
    @17
    @28
    @32
    @59
    @17
    @32
    @47
    recnd
    pncan3d
    eqtr2d
    climadd
    cem
    @1
    cem
    cc
    wcel
    @1
    @57
    trud
    #
    cem
    cG
    climcl
    ax-mp
    addid1i
    syl6breq
    trud
    @60
    pm3.2i
end
