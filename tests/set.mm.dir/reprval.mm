include "cn.mm"
include "cpw.mm"
include "cz.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "wceq.mm"
include "cmap.mm"
include "crab.mm"
include "crepr.mm"
include "cvv.mm"
include "cmpt2.mm"
include "cn0.mm"
include "cmpt.mm"
include "df-repr.mm"
include "a1i.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "eqeq1d.mm"
include "rabeqbidv.mm"
include "mpt2eq3dv.mm"
include "adantl.mm"
include "wcel.mm"
include "nnex.mm"
include "pwex.mm"
include "zex.mm"
include "mpt2ex.mm"
include "fvmptd.mm"
include "wa.mm"
include "simprl.mm"
include "oveq1d.mm"
include "simprr.mm"
include "eqeq2d.mm"
include "ssexd.mm"
include "elpwd.mm"
include "ovex.mm"
include "rabex.mm"
include "ovmpt2d.mm"

theorem reprval
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cM: class M
  let va: setvar a
  let vc: setvar c
  let vb: setvar b
  let vm: setvar m
  let vs: setvar s
  assume reprval.a: |- ( ph -> A C_ NN )
  assume reprval.m: |- ( ph -> M e. ZZ )
  assume reprval.s: |- ( ph -> S e. NN0 )

  disjoint A c
  disjoint M c
  disjoint S a
  disjoint S c
  disjoint a c
  disjoint c ph
  disjoint A b
  disjoint A m
  disjoint b c
  disjoint b m
  disjoint c m
  disjoint M b
  disjoint M m
  disjoint S b
  disjoint S m
  disjoint S s
  disjoint a b
  disjoint a m
  disjoint a s
  disjoint b s
  disjoint c s
  disjoint m s
  disjoint b ph
  disjoint m ph
  disjoint ph s
  assert |- ( ph -> ( A ( repr ` S ) M ) = { c e. ( A ^m ( 0 ..^ S ) ) | sum_ a e. ( 0 ..^ S ) ( c ` a ) = M } )

  proof
    wph
    vb
    vm
    cA
    cM
    cn
    cpw
    #
    cz
    cc0
    cS
    cfzo
    co
    #
    va
    cv
    vc
    cv
    cfv
    #
    va
    csu
    #
    vm
    cv
    #
    wceq
    #
    vc
    vb
    cv
    #
    @1
    cmap
    co
    #
    crab
    #
    @3
    cM
    wceq
    #
    vc
    cA
    @1
    cmap
    co
    #
    crab
    #
    cS
    crepr
    cfv
    cvv
    wph
    vs
    cS
    vb
    vm
    @0
    cz
    cc0
    vs
    cv
    #
    cfzo
    co
    #
    @2
    va
    csu
    #
    @4
    wceq
    #
    vc
    @6
    @13
    cmap
    co
    #
    crab
    #
    cmpt2
    #
    vb
    vm
    @0
    cz
    @8
    cmpt2
    #
    cn0
    crepr
    cvv
    crepr
    vs
    cn0
    @18
    cmpt
    wceq
    wph
    vm
    vs
    va
    vb
    vc
    df-repr
    a1i
    @12
    cS
    wceq
    #
    @18
    @19
    wceq
    wph
    @20
    vb
    vm
    @0
    cz
    @17
    @8
    @20
    @15
    @5
    vc
    @16
    @7
    @20
    @13
    @1
    @6
    cmap
    @12
    cS
    cc0
    cfzo
    oveq2
    #
    oveq2d
    @20
    @14
    @3
    @4
    @20
    @13
    @1
    @2
    va
    @21
    sumeq1d
    eqeq1d
    rabeqbidv
    mpt2eq3dv
    adantl
    reprval.s
    @19
    cvv
    wcel
    wph
    vb
    vm
    @0
    cz
    @8
    cn
    nnex
    pwex
    zex
    mpt2ex
    a1i
    fvmptd
    wph
    @6
    cA
    wceq
    #
    @4
    cM
    wceq
    #
    wa
    wa
    #
    @5
    @9
    vc
    @7
    @10
    @24
    @6
    cA
    @1
    cmap
    wph
    @22
    @23
    simprl
    oveq1d
    @24
    @4
    cM
    @3
    wph
    @22
    @23
    simprr
    eqeq2d
    rabeqbidv
    wph
    cA
    cn
    cvv
    wph
    cA
    cn
    cvv
    cn
    cvv
    wcel
    wph
    nnex
    a1i
    reprval.a
    ssexd
    reprval.a
    elpwd
    reprval.m
    @11
    cvv
    wcel
    wph
    @9
    vc
    @10
    cA
    @1
    cmap
    ovex
    rabex
    a1i
    ovmpt2d
end
