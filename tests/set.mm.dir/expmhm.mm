include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cmpt.mm"
include "wf.mm"
include "caddc.mm"
include "cfv.mm"
include "cmul.mm"
include "wceq.mm"
include "wral.mm"
include "cc0.mm"
include "c1.mm"
include "cmhm.mm"
include "expcl.mm"
include "eqid.mm"
include "fmptd.mm"
include "wa.mm"
include "expadd.mm"
include "3expb.mm"
include "nn0addcl.mm"
include "adantl.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "oveqan12d.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "0nn0.mm"
include "ax-mp.mm"
include "exp0.mm"
include "syl5eq.mm"
include "cmnd.mm"
include "w3a.mm"
include "ccnfld.mm"
include "csubmnd.mm"
include "nn0subm.mm"
include "submmnd.mm"
include "crg.mm"
include "cnring.mm"
include "ringmgp.mm"
include "pm3.2i.mm"
include "cbs.mm"
include "submbas.mm"
include "cnfldbas.mm"
include "mgpbas.mm"
include "cplusg.mm"
include "cnfldadd.mm"
include "ressplusg.mm"
include "cnfldmul.mm"
include "mgpplusg.mm"
include "c0g.mm"
include "cnfld0.mm"
include "subm0.mm"
include "cnfld1.mm"
include "ringidval.mm"
include "ismhm.mm"
include "mpbiran.mm"
include "syl3anbrc.mm"

theorem expmhm
  let vx: setvar x
  let cA: class A
  let cM: class M
  let cN: class N
  let vy: setvar y
  let vz: setvar z
  assume expmhm.1: |- N = ( CCfld |`s NN0 )
  assume expmhm.2: |- M = ( mulGrp ` CCfld )

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint M y
  disjoint M z
  disjoint N y
  disjoint N z
  assert |- ( A e. CC -> ( x e. NN0 |-> ( A ^ x ) ) e. ( N MndHom M ) )

  proof
    cA
    cc
    wcel
    #
    cn0
    cc
    vx
    cn0
    cA
    vx
    cv
    #
    cexp
    co
    #
    cmpt
    #
    wf
    #
    vy
    cv
    #
    vz
    cv
    #
    caddc
    co
    #
    @3
    cfv
    #
    @5
    @3
    cfv
    #
    @6
    @3
    cfv
    #
    cmul
    co
    #
    wceq
    #
    vz
    cn0
    wral
    vy
    cn0
    wral
    #
    cc0
    @3
    cfv
    #
    c1
    wceq
    #
    @3
    cN
    cM
    cmhm
    co
    wcel
    #
    @0
    vx
    cn0
    @2
    cc
    @3
    cA
    @1
    expcl
    @3
    eqid
    #
    fmptd
    @0
    @12
    vy
    vz
    cn0
    cn0
    @0
    @5
    cn0
    wcel
    #
    @6
    cn0
    wcel
    #
    wa
    #
    wa
    #
    cA
    @7
    cexp
    co
    #
    cA
    @5
    cexp
    co
    #
    cA
    @6
    cexp
    co
    #
    cmul
    co
    #
    @8
    @11
    @0
    @18
    @19
    @22
    @25
    wceq
    cA
    @5
    @6
    expadd
    3expb
    @21
    @7
    cn0
    wcel
    #
    @8
    @22
    wceq
    @20
    @26
    @0
    @5
    @6
    nn0addcl
    adantl
    vx
    @7
    @2
    @22
    cn0
    @3
    @1
    @7
    cA
    cexp
    oveq2
    @17
    cA
    @7
    cexp
    ovex
    fvmpt
    syl
    @20
    @11
    @25
    wceq
    @0
    @18
    @19
    @9
    @23
    @10
    @24
    cmul
    vx
    @5
    @2
    @23
    cn0
    @3
    @1
    @5
    cA
    cexp
    oveq2
    @17
    cA
    @5
    cexp
    ovex
    fvmpt
    vx
    @6
    @2
    @24
    cn0
    @3
    @1
    @6
    cA
    cexp
    oveq2
    @17
    cA
    @6
    cexp
    ovex
    fvmpt
    oveqan12d
    adantl
    3eqtr4d
    ralrimivva
    @0
    @14
    cA
    cc0
    cexp
    co
    #
    c1
    cc0
    cn0
    wcel
    @14
    @27
    wceq
    0nn0
    vx
    cc0
    @2
    @27
    cn0
    @3
    @1
    cc0
    cA
    cexp
    oveq2
    @17
    cA
    cc0
    cexp
    ovex
    fvmpt
    ax-mp
    cA
    exp0
    syl5eq
    @16
    cN
    cmnd
    wcel
    #
    cM
    cmnd
    wcel
    #
    wa
    @4
    @13
    @15
    w3a
    @28
    @29
    cn0
    ccnfld
    csubmnd
    cfv
    #
    wcel
    #
    @28
    nn0subm
    cn0
    cN
    ccnfld
    expmhm.1
    submmnd
    ax-mp
    ccnfld
    crg
    wcel
    @29
    cnring
    ccnfld
    cM
    expmhm.2
    ringmgp
    ax-mp
    pm3.2i
    vy
    vz
    cn0
    cc
    caddc
    cmul
    cN
    cM
    @3
    c1
    cc0
    @31
    cn0
    cN
    cbs
    cfv
    wceq
    nn0subm
    cn0
    cN
    ccnfld
    expmhm.1
    submbas
    ax-mp
    cc
    ccnfld
    cM
    expmhm.2
    cnfldbas
    mgpbas
    @31
    caddc
    cN
    cplusg
    cfv
    wceq
    nn0subm
    cn0
    caddc
    ccnfld
    cN
    @30
    expmhm.1
    cnfldadd
    ressplusg
    ax-mp
    ccnfld
    cmul
    cM
    expmhm.2
    cnfldmul
    mgpplusg
    @31
    cc0
    cN
    c0g
    cfv
    wceq
    nn0subm
    cn0
    cN
    ccnfld
    cc0
    expmhm.1
    cnfld0
    subm0
    ax-mp
    ccnfld
    c1
    cM
    expmhm.2
    cnfld1
    ringidval
    ismhm
    mpbiran
    syl3anbrc
end
