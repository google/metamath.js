include "cmpt.mm"
include "cmin.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "a1i.mm"
include "cv.mm"
include "wa.mm"
include "csb.mm"
include "cc.mm"
include "wceq.mm"
include "simpr.mm"
include "wi.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcv.mm"
include "nfcsb1.mm"
include "nfel1.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "eqid.mm"
include "fvmptf.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "nfel.mm"
include "ovexd.mm"
include "nfov.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "climsub.mm"

theorem climsubmpt
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  assume climsubmpt.k: |- F/ k ph
  assume climsubmpt.z: |- Z = ( ZZ>= ` M )
  assume climsubmpt.m: |- ( ph -> M e. ZZ )
  assume climsubmpt.a: |- ( ( ph /\ k e. Z ) -> A e. CC )
  assume climsubmpt.b: |- ( ( ph /\ k e. Z ) -> B e. CC )
  assume climsubmpt.c: |- ( ph -> ( k e. Z |-> A ) ~~> C )
  assume climsubmpt.d: |- ( ph -> ( k e. Z |-> B ) ~~> D )

  disjoint Z k
  disjoint A j
  disjoint B j
  disjoint C j
  disjoint D j
  disjoint M j
  disjoint Z j
  disjoint j k
  disjoint j ph
  assert |- ( ph -> ( k e. Z |-> ( A - B ) ) ~~> ( C - D ) )

  proof
    wph
    cC
    cD
    vj
    vk
    cZ
    cA
    cmpt
    #
    vk
    cZ
    cB
    cmpt
    #
    vk
    cZ
    cA
    cB
    cmin
    co
    #
    cmpt
    #
    cM
    cvv
    cZ
    climsubmpt.z
    climsubmpt.m
    climsubmpt.c
    @3
    cvv
    wcel
    wph
    vk
    cZ
    @2
    cZ
    cM
    cuz
    cfv
    cvv
    climsubmpt.z
    cM
    cuz
    fvex
    eqeltri
    mptex
    a1i
    climsubmpt.d
    wph
    vj
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @4
    @0
    cfv
    #
    vk
    @4
    cA
    csb
    #
    cc
    @6
    @5
    @8
    cc
    wcel
    #
    @7
    @8
    wceq
    wph
    @5
    simpr
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
    cA
    cc
    wcel
    #
    wi
    @6
    @9
    wi
    vk
    vj
    @6
    @9
    vk
    wph
    @5
    vk
    climsubmpt.k
    @5
    vk
    nfv
    nfan
    #
    vk
    @8
    cc
    vk
    @4
    cA
    vk
    @4
    nfcv
    #
    nfcsb1
    #
    nfel1
    nfim
    @11
    @4
    wceq
    #
    @13
    @6
    @14
    @9
    @18
    @12
    @5
    wph
    @11
    @4
    cZ
    eleq1
    anbi2d
    #
    @18
    cA
    @8
    cc
    vk
    @4
    cA
    csbeq1a
    #
    eleq1d
    imbi12d
    climsubmpt.a
    chvar
    #
    vk
    @4
    cA
    @8
    cZ
    @0
    cc
    @16
    @17
    @20
    @0
    eqid
    fvmptf
    syl2anc
    #
    @21
    eqeltrd
    @6
    @4
    @1
    cfv
    #
    vk
    @4
    cB
    csb
    #
    cc
    @6
    @5
    @24
    cc
    wcel
    #
    @23
    @24
    wceq
    @10
    @13
    cB
    cc
    wcel
    #
    wi
    @6
    @25
    wi
    vk
    vj
    @6
    @25
    vk
    @15
    vk
    @24
    cc
    vk
    @4
    cB
    @16
    nfcsb1
    #
    vk
    cc
    nfcv
    nfel
    nfim
    @18
    @13
    @6
    @26
    @25
    @19
    @18
    cB
    @24
    cc
    vk
    @4
    cB
    csbeq1a
    #
    eleq1d
    imbi12d
    climsubmpt.b
    chvar
    #
    vk
    @4
    cB
    @24
    cZ
    @1
    cc
    @16
    @27
    @28
    @1
    eqid
    fvmptf
    syl2anc
    #
    @29
    eqeltrd
    @6
    @4
    @3
    cfv
    #
    @8
    @24
    cmin
    co
    #
    @7
    @23
    cmin
    co
    @6
    @5
    @32
    cvv
    wcel
    @31
    @32
    wceq
    @10
    @6
    @8
    @24
    cmin
    ovexd
    vk
    @4
    @2
    @32
    cZ
    @3
    cvv
    @16
    vk
    @8
    @24
    cmin
    @17
    vk
    cmin
    nfcv
    @27
    nfov
    @18
    cA
    @8
    cB
    @24
    cmin
    @20
    @28
    oveq12d
    @3
    eqid
    fvmptf
    syl2anc
    @6
    @7
    @8
    @23
    @24
    cmin
    @22
    @30
    oveq12d
    eqtr4d
    climsub
end
