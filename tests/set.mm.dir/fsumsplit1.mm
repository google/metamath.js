include "csu.mm"
include "csn.mm"
include "cdif.mm"
include "cun.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "uncom.mm"
include "a1i.mm"
include "wss.mm"
include "snssd.mm"
include "undif.mm"
include "sylib.mm"
include "eqidd.mm"
include "3eqtrrd.mm"
include "sumeq1d.mm"
include "cfn.mm"
include "wcel.mm"
include "diffi.mm"
include "syl.mm"
include "neldifsnd.mm"
include "cv.mm"
include "wa.mm"
include "cc.mm"
include "simpl.mm"
include "eldifi.mm"
include "adantl.mm"
include "syl2anc.mm"
include "csb.mm"
include "wnfc.mm"
include "simpr.mm"
include "csbiedf.mm"
include "eqcomd.mm"
include "ancli.mm"
include "wi.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcsb1.mm"
include "nfel.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "vtoclgf.mm"
include "sylc.mm"
include "eqeltrd.mm"
include "fsumsplitsn.mm"
include "fsumclf.mm"
include "addcomd.mm"
include "3eqtrd.mm"

theorem fsumsplit1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  assume fsumsplit1.kph: |- F/ k ph
  assume fsumsplit1.kd: |- F/_ k D
  assume fsumsplit1.a: |- ( ph -> A e. Fin )
  assume fsumsplit1.b: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume fsumsplit1.c: |- ( ph -> C e. A )
  assume fsumsplit1.bd: |- ( k = C -> B = D )

  disjoint A k
  disjoint C k
  assert |- ( ph -> sum_ k e. A B = ( D + sum_ k e. ( A \ { C } ) B ) )

  proof
    wph
    cA
    cB
    vk
    csu
    cA
    cC
    csn
    #
    cdif
    #
    @0
    cun
    #
    cB
    vk
    csu
    @1
    cB
    vk
    csu
    #
    cD
    caddc
    co
    cD
    @3
    caddc
    co
    wph
    cA
    @2
    cB
    vk
    wph
    @2
    @0
    @1
    cun
    #
    cA
    cA
    @2
    @4
    wceq
    wph
    @1
    @0
    uncom
    a1i
    wph
    @0
    cA
    wss
    @4
    cA
    wceq
    wph
    cC
    cA
    fsumsplit1.c
    snssd
    @0
    cA
    undif
    sylib
    wph
    cA
    eqidd
    3eqtrrd
    sumeq1d
    wph
    @1
    cC
    cB
    cD
    vk
    cA
    fsumsplit1.kph
    fsumsplit1.kd
    wph
    cA
    cfn
    wcel
    @1
    cfn
    wcel
    fsumsplit1.a
    cA
    @0
    diffi
    syl
    #
    fsumsplit1.c
    wph
    cC
    cA
    neldifsnd
    wph
    vk
    cv
    #
    @1
    wcel
    #
    wa
    wph
    @6
    cA
    wcel
    #
    cB
    cc
    wcel
    #
    wph
    @7
    simpl
    @7
    @8
    wph
    @6
    cA
    @0
    eldifi
    adantl
    fsumsplit1.b
    syl2anc
    #
    fsumsplit1.bd
    wph
    cD
    vk
    cC
    cB
    csb
    #
    cc
    wph
    @11
    cD
    wph
    vk
    cC
    cB
    cD
    cA
    fsumsplit1.kph
    vk
    cD
    wnfc
    wph
    fsumsplit1.kd
    a1i
    fsumsplit1.c
    wph
    @6
    cC
    wceq
    #
    wa
    @12
    cB
    cD
    wceq
    wph
    @12
    simpr
    fsumsplit1.bd
    syl
    csbiedf
    eqcomd
    wph
    cC
    cA
    wcel
    #
    wph
    @13
    wa
    #
    @11
    cc
    wcel
    #
    fsumsplit1.c
    wph
    @13
    fsumsplit1.c
    ancli
    wph
    @8
    wa
    #
    @9
    wi
    @14
    @15
    wi
    vk
    cC
    cA
    vk
    cC
    nfcv
    #
    @14
    @15
    vk
    wph
    @13
    vk
    fsumsplit1.kph
    @13
    vk
    nfv
    nfan
    vk
    @11
    cc
    vk
    cC
    cB
    @17
    nfcsb1
    vk
    cc
    nfcv
    nfel
    nfim
    @12
    @16
    @14
    @9
    @15
    @12
    @8
    @13
    wph
    @6
    cC
    cA
    eleq1
    anbi2d
    @12
    cB
    @11
    cc
    vk
    cC
    cB
    csbeq1a
    eleq1d
    imbi12d
    fsumsplit1.b
    vtoclgf
    sylc
    eqeltrd
    #
    fsumsplitsn
    wph
    @3
    cD
    wph
    @1
    cB
    vk
    fsumsplit1.kph
    @5
    @10
    fsumclf
    @18
    addcomd
    3eqtrd
end
