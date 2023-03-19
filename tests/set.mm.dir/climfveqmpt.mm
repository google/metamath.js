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
include "wss.mm"
include "adantr.mm"
include "simpr.mm"
include "sseldd.mm"
include "nfel.mm"
include "eleq1d.mm"
include "eqid.mm"
include "fvmptf.mm"
include "syl2anc.mm"
include "syldan.mm"
include "3eqtr4d.mm"
include "climfveq.mm"

theorem climfveqmpt
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
  assume climfveqmpt.k: |- F/ k ph
  assume climfveqmpt.m: |- ( ph -> M e. ZZ )
  assume climfveqmpt.z: |- Z = ( ZZ>= ` M )
  assume climfveqmpt.A: |- ( ph -> A e. R )
  assume climfveqmpt.i: |- ( ph -> Z C_ A )
  assume climfveqmpt.b: |- ( ( ph /\ k e. A ) -> B e. V )
  assume climfveqmpt.t: |- ( ph -> C e. S )
  assume climfveqmpt.l: |- ( ph -> Z C_ C )
  assume climfveqmpt.c: |- ( ( ph /\ k e. C ) -> D e. W )
  assume climfveqmpt.e: |- ( ( ph /\ k e. Z ) -> B = D )

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
  assert |- ( ph -> ( ~~> ` ( k e. A |-> B ) ) = ( ~~> ` ( k e. C |-> D ) ) )

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
    climfveqmpt.z
    wph
    vk
    cA
    cB
    cR
    climfveqmpt.A
    mptexd
    wph
    vk
    cC
    cD
    cS
    climfveqmpt.t
    mptexd
    climfveqmpt.m
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
    climfveqmpt.k
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
    vk
    @2
    nfcv
    #
    nfcsb1
    #
    vk
    @2
    cD
    @14
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
    climfveqmpt.e
    chvar
    wph
    @3
    @2
    cA
    wcel
    #
    @7
    @5
    wceq
    #
    @4
    cZ
    cA
    @2
    wph
    cZ
    cA
    wss
    @3
    climfveqmpt.i
    adantr
    wph
    @3
    simpr
    #
    sseldd
    wph
    @20
    wa
    #
    @20
    @5
    cV
    wcel
    #
    @21
    wph
    @20
    simpr
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
    @23
    @24
    wi
    vk
    vj
    @23
    @24
    vk
    wph
    @20
    vk
    climfveqmpt.k
    @20
    vk
    nfv
    nfan
    vk
    @5
    cV
    @15
    vk
    cV
    nfcv
    nfel
    nfim
    @17
    @26
    @23
    @27
    @24
    @17
    @25
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
    climfveqmpt.b
    chvar
    vk
    @2
    cB
    @5
    cA
    @0
    cV
    @14
    @15
    @18
    @0
    eqid
    fvmptf
    syl2anc
    syldan
    wph
    @3
    @2
    cC
    wcel
    #
    @8
    @6
    wceq
    #
    @4
    cZ
    cC
    @2
    wph
    cZ
    cC
    wss
    @3
    climfveqmpt.l
    adantr
    @22
    sseldd
    wph
    @28
    wa
    #
    @28
    @6
    cW
    wcel
    #
    @29
    wph
    @28
    simpr
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
    @30
    @31
    wi
    vk
    vj
    @30
    @31
    vk
    wph
    @28
    vk
    climfveqmpt.k
    @28
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
    @33
    @30
    @34
    @31
    @17
    @32
    @28
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
    climfveqmpt.c
    chvar
    vk
    @2
    cD
    @6
    cC
    @1
    cW
    @14
    @16
    @19
    @1
    eqid
    fvmptf
    syl2anc
    syldan
    3eqtr4d
    climfveq
end
