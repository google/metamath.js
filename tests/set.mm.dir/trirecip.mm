include "cn.mm"
include "c2.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "cdiv.mm"
include "csu.mm"
include "wcel.mm"
include "2cnd.mm"
include "peano2nn.mm"
include "nnmulcl.mm"
include "mpdan.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divrecd.mm"
include "sumeq2i.mm"
include "wceq.mm"
include "wtru.mm"
include "cmpt.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cfv.mm"
include "id.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "oveq2d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "cc.mm"
include "nnrecred.mm"
include "recnd.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "cdm.mm"
include "trireciplem.mm"
include "a1i.mm"
include "climrel.mm"
include "releldmi.mm"
include "syl.mm"
include "isummulc2.mm"
include "isumclim.mm"
include "eqtr3d.mm"
include "trud.mm"
include "2t1e2.mm"
include "3eqtri.mm"

theorem trirecip
  let vk: setvar k
  let vn: setvar n


  assert |- sum_ k e. NN ( 2 / ( k x. ( k + 1 ) ) ) = 2

  proof
    cn
    c2
    vk
    cv
    #
    @0
    c1
    caddc
    co
    #
    cmul
    co
    #
    cdiv
    co
    #
    vk
    csu
    cn
    c2
    c1
    @2
    cdiv
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    c2
    c1
    cmul
    co
    #
    c2
    cn
    @3
    @5
    vk
    @0
    cn
    wcel
    #
    c2
    @2
    @8
    2cnd
    @8
    @2
    @8
    @1
    cn
    wcel
    @2
    cn
    wcel
    @0
    peano2nn
    @0
    @1
    nnmulcl
    mpdan
    #
    nncnd
    @8
    @2
    @9
    nnne0d
    divrecd
    sumeq2i
    @6
    @7
    wceq
    wtru
    c2
    cn
    @4
    vk
    csu
    #
    cmul
    co
    @6
    @7
    wtru
    @4
    c2
    vk
    vn
    cn
    c1
    vn
    cv
    #
    @11
    c1
    caddc
    co
    #
    cmul
    co
    #
    cdiv
    co
    #
    cmpt
    #
    c1
    cn
    nnuz
    wtru
    1zzd
    #
    @8
    @0
    @15
    cfv
    @4
    wceq
    wtru
    vn
    @0
    @14
    @4
    cn
    @15
    @11
    @0
    wceq
    #
    @13
    @2
    c1
    cdiv
    @17
    @11
    @0
    @12
    @1
    cmul
    @17
    id
    @11
    @0
    c1
    caddc
    oveq1
    oveq12d
    oveq2d
    @15
    eqid
    #
    c1
    @2
    cdiv
    ovex
    fvmpt
    adantl
    #
    @8
    @4
    cc
    wcel
    wtru
    @8
    @4
    @8
    @2
    @9
    nnrecred
    recnd
    adantl
    #
    wtru
    caddc
    @15
    c1
    cseq
    #
    c1
    cli
    wbr
    #
    @21
    cli
    cdm
    wcel
    @22
    wtru
    vn
    @15
    @18
    trireciplem
    a1i
    #
    @21
    c1
    cli
    climrel
    releldmi
    syl
    wtru
    2cnd
    isummulc2
    wtru
    @10
    c1
    c2
    cmul
    wtru
    @4
    c1
    vk
    @15
    c1
    cn
    nnuz
    @16
    @19
    @20
    @23
    isumclim
    oveq2d
    eqtr3d
    trud
    2t1e2
    3eqtri
end
