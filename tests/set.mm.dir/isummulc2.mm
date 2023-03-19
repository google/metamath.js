include "cmul.mm"
include "co.mm"
include "csu.mm"
include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "sumfc.mm"
include "wcel.mm"
include "wa.mm"
include "eqidd.mm"
include "cc.mm"
include "adantr.mm"
include "mulcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "isumclim2.mm"
include "wral.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "sylan.mm"
include "cvv.mm"
include "simpr.mm"
include "ovex.mm"
include "fvmpt2.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "nffvmpt1.mm"
include "nfeq1.mm"
include "eqeq12d.mm"
include "rspc.mm"
include "mpan9.mm"
include "isermulc2.mm"
include "isumclim.mm"
include "syl5reqr.mm"

theorem isummulc2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vm: setvar m
  assume isumcl.1: |- Z = ( ZZ>= ` M )
  assume isumcl.2: |- ( ph -> M e. ZZ )
  assume isumcl.3: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = A )
  assume isumcl.4: |- ( ( ph /\ k e. Z ) -> A e. CC )
  assume isumcl.5: |- ( ph -> seq M ( + , F ) e. dom ~~> )
  assume summulc.6: |- ( ph -> B e. CC )

  disjoint B k
  disjoint F k
  disjoint k ph
  disjoint Z k
  disjoint M k
  disjoint A m
  disjoint k m
  disjoint B m
  disjoint F m
  disjoint m ph
  disjoint Z m
  disjoint M m
  assert |- ( ph -> ( B x. sum_ k e. Z A ) = sum_ k e. Z ( B x. A ) )

  proof
    wph
    cZ
    cB
    cA
    cmul
    co
    #
    vk
    csu
    cZ
    vm
    cv
    #
    vk
    cZ
    @0
    cmpt
    #
    cfv
    #
    vm
    csu
    cB
    cZ
    cA
    vk
    csu
    #
    cmul
    co
    #
    cZ
    @0
    vm
    vk
    sumfc
    wph
    @3
    @5
    vm
    @2
    cM
    cZ
    isumcl.1
    isumcl.2
    wph
    @1
    cZ
    wcel
    #
    wa
    @3
    eqidd
    wph
    cZ
    cc
    @1
    @2
    wph
    vk
    cZ
    @0
    cc
    @2
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
    cA
    wph
    cB
    cc
    wcel
    @8
    summulc.6
    adantr
    isumcl.4
    mulcld
    @2
    eqid
    #
    fmptd
    ffvelrnda
    wph
    @4
    cB
    vm
    cF
    @2
    cM
    cZ
    isumcl.1
    isumcl.2
    summulc.6
    wph
    cA
    vk
    cF
    cM
    cZ
    isumcl.1
    isumcl.2
    isumcl.3
    isumcl.4
    isumcl.5
    isumclim2
    wph
    @7
    cF
    cfv
    #
    cc
    wcel
    #
    vk
    cZ
    wral
    @6
    @1
    cF
    cfv
    #
    cc
    wcel
    #
    wph
    @12
    vk
    cZ
    @9
    @11
    cA
    cc
    isumcl.3
    isumcl.4
    eqeltrd
    ralrimiva
    @12
    @14
    vk
    @1
    cZ
    @7
    @1
    wceq
    #
    @11
    @13
    cc
    @7
    @1
    cF
    fveq2
    #
    eleq1d
    rspccva
    sylan
    wph
    @7
    @2
    cfv
    #
    cB
    @11
    cmul
    co
    #
    wceq
    #
    vk
    cZ
    wral
    @6
    @3
    cB
    @13
    cmul
    co
    #
    wceq
    #
    wph
    @19
    vk
    cZ
    @9
    @17
    @0
    @18
    @9
    @8
    @0
    cvv
    wcel
    @17
    @0
    wceq
    wph
    @8
    simpr
    cB
    cA
    cmul
    ovex
    vk
    cZ
    @0
    cvv
    @2
    @10
    fvmpt2
    sylancl
    @9
    @11
    cA
    cB
    cmul
    isumcl.3
    oveq2d
    eqtr4d
    ralrimiva
    @19
    @21
    vk
    @1
    cZ
    vk
    @3
    @20
    vk
    cZ
    @0
    @1
    nffvmpt1
    nfeq1
    @15
    @17
    @3
    @18
    @20
    @7
    @1
    @2
    fveq2
    @15
    @11
    @13
    cB
    cmul
    @16
    oveq2d
    eqeq12d
    rspc
    mpan9
    isermulc2
    isumclim
    syl5reqr
end
