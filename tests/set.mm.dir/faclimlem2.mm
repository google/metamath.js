include "cn0.mm"
include "wcel.mm"
include "cmul.mm"
include "cn.mm"
include "c1.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cmpt.mm"
include "cseq.mm"
include "cli.mm"
include "faclimlem1.mm"
include "cvv.mm"
include "nnuz.mm"
include "1zzd.mm"
include "1cnd.mm"
include "nn0p1nn.mm"
include "nnzd.mm"
include "nnex.mm"
include "mptex.mm"
include "a1i.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "divcnvlin.mm"
include "nncnd.mm"
include "cc.mm"
include "wa.mm"
include "peano2nn.mm"
include "nnred.mm"
include "simpr.mm"
include "adantr.mm"
include "nnaddcld.mm"
include "nndivred.mm"
include "recnd.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "climmulc2.mm"
include "mulid1d.mm"
include "breqtrd.mm"
include "eqbrtrd.mm"

theorem faclimlem2
  let vn: setvar n
  let cM: class M
  let vk: setvar k
  let vm: setvar m

  disjoint M n
  disjoint k m
  disjoint M k
  disjoint M m
  assert |- ( M e. NN0 -> seq 1 ( x. , ( n e. NN |-> ( ( ( 1 + ( M / n ) ) x. ( 1 + ( 1 / n ) ) ) / ( 1 + ( ( M + 1 ) / n ) ) ) ) ) ~~> ( M + 1 ) )

  proof
    cM
    cn0
    wcel
    #
    cmul
    vn
    cn
    c1
    cM
    vn
    cv
    #
    cdiv
    co
    caddc
    co
    c1
    c1
    @1
    cdiv
    co
    caddc
    co
    cmul
    co
    c1
    cM
    c1
    caddc
    co
    #
    @1
    cdiv
    co
    caddc
    co
    cdiv
    co
    cmpt
    c1
    cseq
    vm
    cn
    @2
    vm
    cv
    #
    c1
    caddc
    co
    #
    @3
    @2
    caddc
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    #
    @2
    cli
    vm
    vn
    cM
    faclimlem1
    @0
    @8
    @2
    c1
    cmul
    co
    @2
    cli
    @0
    c1
    @2
    vk
    vm
    cn
    @6
    cmpt
    #
    @8
    c1
    cvv
    cn
    nnuz
    @0
    1zzd
    #
    @0
    c1
    @2
    vk
    @9
    c1
    cvv
    cn
    nnuz
    @10
    @0
    1cnd
    @0
    @2
    cM
    nn0p1nn
    #
    nnzd
    @9
    cvv
    wcel
    @0
    vm
    cn
    @6
    nnex
    mptex
    a1i
    vk
    cv
    #
    cn
    wcel
    #
    @12
    @9
    cfv
    #
    @12
    c1
    caddc
    co
    #
    @12
    @2
    caddc
    co
    #
    cdiv
    co
    #
    wceq
    @0
    vm
    @12
    @6
    @17
    cn
    @9
    vm
    vk
    weq
    #
    @4
    @15
    @5
    @16
    cdiv
    @3
    @12
    c1
    caddc
    oveq1
    @3
    @12
    @2
    caddc
    oveq1
    oveq12d
    #
    @9
    eqid
    #
    @15
    @16
    cdiv
    ovex
    fvmpt
    #
    adantl
    divcnvlin
    @0
    @2
    @11
    nncnd
    #
    @8
    cvv
    wcel
    @0
    vm
    cn
    @7
    nnex
    mptex
    a1i
    @0
    cn
    cc
    @12
    @9
    @0
    vm
    cn
    @6
    cc
    @9
    @0
    @3
    cn
    wcel
    #
    wa
    #
    @6
    @24
    @4
    @5
    @24
    @4
    @23
    @4
    cn
    wcel
    @0
    @3
    peano2nn
    adantl
    nnred
    @24
    @3
    @2
    @0
    @23
    simpr
    @0
    @2
    cn
    wcel
    @23
    @11
    adantr
    nnaddcld
    nndivred
    recnd
    @20
    fmptd
    ffvelrnda
    @13
    @12
    @8
    cfv
    #
    @2
    @14
    cmul
    co
    #
    wceq
    @0
    @13
    @25
    @2
    @17
    cmul
    co
    #
    @26
    vm
    @12
    @7
    @27
    cn
    @8
    @18
    @6
    @17
    @2
    cmul
    @19
    oveq2d
    @8
    eqid
    @2
    @17
    cmul
    ovex
    fvmpt
    @13
    @14
    @17
    @2
    cmul
    @21
    oveq2d
    eqtr4d
    adantl
    climmulc2
    @0
    @2
    @22
    mulid1d
    breqtrd
    eqbrtrd
end
