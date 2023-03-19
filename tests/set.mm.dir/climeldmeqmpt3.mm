include "cmpt.mm"
include "cvv.mm"
include "mptexd.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "csb.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcsb1v.mm"
include "nfcv.mm"
include "nfcsb1.mm"
include "nfeq.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "csbeq1a.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "sselda.mm"
include "nfel.mm"
include "eleq1d.mm"
include "eqid.mm"
include "fvmptf.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "3eqtr4d.mm"
include "climeldmeq.mm"

theorem climeldmeqmpt3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cU: class U
  let vk: setvar k
  let cM: class M
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vj: setvar j
  assume climeldmeqmpt3.k: |- F/ k ph
  assume climeldmeqmpt3.m: |- ( ph -> M e. ZZ )
  assume climeldmeqmpt3.z: |- Z = ( ZZ>= ` M )
  assume climeldmeqmpt3.a: |- ( ph -> A e. V )
  assume climeldmeqmpt3.c: |- ( ph -> C e. W )
  assume climeldmeqmpt3.i: |- ( ph -> Z C_ A )
  assume climeldmeqmpt3.s: |- ( ph -> Z C_ C )
  assume climeldmeqmpt3.b: |- ( ( ph /\ k e. Z ) -> B e. U )
  assume climeldmeqmpt3.e: |- ( ( ph /\ k e. Z ) -> B = D )

  disjoint A k
  disjoint C k
  disjoint U k
  disjoint Z k
  disjoint A j
  disjoint j k
  disjoint B j
  disjoint C j
  disjoint D j
  disjoint Z j
  disjoint j ph
  assert |- ( ph -> ( ( k e. A |-> B ) e. dom ~~> <-> ( k e. C |-> D ) e. dom ~~> ) )

  proof
    wph
    vj
    vk
    cA
    cB
    cmpt
    #
    vk
    cC
    cD
    cmpt
    #
    cM
    cvv
    cvv
    cZ
    climeldmeqmpt3.z
    wph
    vk
    cA
    cB
    cV
    climeldmeqmpt3.a
    mptexd
    wph
    vk
    cC
    cD
    cW
    climeldmeqmpt3.c
    mptexd
    climeldmeqmpt3.m
    wph
    vj
    cv
    #
    cZ
    wcel
    #
    wa
    #
    vk
    @2
    cB
    csb
    #
    vk
    @2
    cD
    csb
    #
    @2
    @0
    cfv
    #
    @2
    @1
    cfv
    #
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    cB
    cD
    wceq
    #
    wi
    @4
    @5
    @6
    wceq
    #
    wi
    vk
    vj
    @4
    @13
    vk
    wph
    @3
    vk
    climeldmeqmpt3.k
    @3
    vk
    nfv
    nfan
    #
    vk
    @5
    @6
    vk
    @2
    cB
    nfcsb1v
    #
    vk
    @2
    cD
    vk
    @2
    nfcv
    #
    nfcsb1
    #
    nfeq
    nfim
    @9
    @2
    wceq
    #
    @11
    @4
    @12
    @13
    @18
    @10
    @3
    wph
    @9
    @2
    cZ
    eleq1
    anbi2d
    #
    @18
    cB
    @5
    cD
    @6
    vk
    @2
    cB
    csbeq1a
    #
    vk
    @2
    cD
    csbeq1a
    #
    eqeq12d
    imbi12d
    climeldmeqmpt3.e
    chvar
    #
    @4
    @2
    cA
    wcel
    @5
    cU
    wcel
    #
    @7
    @5
    wceq
    wph
    cZ
    cA
    @2
    climeldmeqmpt3.i
    sselda
    @11
    cB
    cU
    wcel
    #
    wi
    @4
    @23
    wi
    vk
    vj
    @4
    @23
    vk
    @14
    vk
    @5
    cU
    @15
    vk
    cU
    nfcv
    nfel
    nfim
    @18
    @11
    @4
    @24
    @23
    @19
    @18
    cB
    @5
    cU
    @20
    eleq1d
    imbi12d
    climeldmeqmpt3.b
    chvar
    #
    vk
    @2
    cB
    @5
    cA
    @0
    cU
    @16
    vk
    @2
    cB
    @16
    nfcsb1
    @20
    @0
    eqid
    fvmptf
    syl2anc
    @4
    @2
    cC
    wcel
    @6
    cU
    wcel
    @8
    @6
    wceq
    wph
    cZ
    cC
    @2
    climeldmeqmpt3.s
    sselda
    @4
    @5
    @6
    cU
    @22
    @25
    eqeltrrd
    vk
    @2
    cD
    @6
    cC
    @1
    cU
    @16
    @17
    @21
    @1
    eqid
    fvmptf
    syl2anc
    3eqtr4d
    climeldmeq
end
