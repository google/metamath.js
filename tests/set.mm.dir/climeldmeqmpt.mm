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
include "syldan.mm"
include "eqid.mm"
include "fvmptf.mm"
include "syl2anc.mm"
include "3eqtr4d.mm"
include "climeldmeq.mm"

theorem climeldmeqmpt
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let vk: setvar k
  let cM: class M
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vj: setvar j
  assume climeldmeqmpt.k: |- F/ k ph
  assume climeldmeqmpt.m: |- ( ph -> M e. ZZ )
  assume climeldmeqmpt.z: |- Z = ( ZZ>= ` M )
  assume climeldmeqmpt.a: |- ( ph -> A e. R )
  assume climeldmeqmpt.i: |- ( ph -> Z C_ A )
  assume climeldmeqmpt.b: |- ( ( ph /\ k e. A ) -> B e. V )
  assume climeldmeqmpt.t: |- ( ph -> C e. S )
  assume climeldmeqmpt.l: |- ( ph -> Z C_ C )
  assume climeldmeqmpt.c: |- ( ( ph /\ k e. C ) -> D e. W )
  assume climeldmeqmpt.e: |- ( ( ph /\ k e. Z ) -> B = D )

  disjoint A k
  disjoint C k
  disjoint V k
  disjoint W k
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
    climeldmeqmpt.z
    wph
    vk
    cA
    cB
    cR
    climeldmeqmpt.a
    mptexd
    wph
    vk
    cC
    cD
    cS
    climeldmeqmpt.t
    mptexd
    climeldmeqmpt.m
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
    climeldmeqmpt.k
    @3
    vk
    nfv
    nfan
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
    @17
    @10
    @3
    wph
    @9
    @2
    cZ
    eleq1
    anbi2d
    @17
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
    climeldmeqmpt.e
    chvar
    @4
    @2
    cA
    wcel
    #
    @5
    cV
    wcel
    #
    @7
    @5
    wceq
    wph
    cZ
    cA
    @2
    climeldmeqmpt.i
    sselda
    #
    wph
    @3
    @20
    @21
    @22
    wph
    @9
    cA
    wcel
    #
    wa
    #
    cB
    cV
    wcel
    #
    wi
    wph
    @20
    wa
    #
    @21
    wi
    vk
    vj
    @26
    @21
    vk
    wph
    @20
    vk
    climeldmeqmpt.k
    @20
    vk
    nfv
    nfan
    vk
    @5
    cV
    @14
    vk
    cV
    nfcv
    nfel
    nfim
    @17
    @24
    @26
    @25
    @21
    @17
    @23
    @20
    wph
    @9
    @2
    cA
    eleq1
    anbi2d
    @17
    cB
    @5
    cV
    @18
    eleq1d
    imbi12d
    climeldmeqmpt.b
    chvar
    syldan
    vk
    @2
    cB
    @5
    cA
    @0
    cV
    @15
    vk
    @2
    cB
    @15
    nfcsb1
    @18
    @0
    eqid
    fvmptf
    syl2anc
    @4
    @2
    cC
    wcel
    #
    @6
    cW
    wcel
    #
    @8
    @6
    wceq
    wph
    cZ
    cC
    @2
    climeldmeqmpt.l
    sselda
    #
    wph
    @3
    @27
    @28
    @29
    wph
    @9
    cC
    wcel
    #
    wa
    #
    cD
    cW
    wcel
    #
    wi
    wph
    @27
    wa
    #
    @28
    wi
    vk
    vj
    @33
    @28
    vk
    wph
    @27
    vk
    climeldmeqmpt.k
    @27
    vk
    nfv
    nfan
    vk
    @6
    cW
    @16
    vk
    cW
    nfcv
    nfel
    nfim
    @17
    @31
    @33
    @32
    @28
    @17
    @30
    @27
    wph
    @9
    @2
    cC
    eleq1
    anbi2d
    @17
    cD
    @6
    cW
    @19
    eleq1d
    imbi12d
    climeldmeqmpt.c
    chvar
    syldan
    vk
    @2
    cD
    @6
    cC
    @1
    cW
    @15
    @16
    @19
    @1
    eqid
    fvmptf
    syl2anc
    3eqtr4d
    climeldmeq
end
