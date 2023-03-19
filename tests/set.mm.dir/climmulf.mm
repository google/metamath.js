include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cc.mm"
include "wi.mm"
include "nfcv.mm"
include "nfel1.mm"
include "nfan.mm"
include "nffv.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "cmul.mm"
include "co.mm"
include "nfov.mm"
include "nfeq.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "climmul.mm"

theorem climmulf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vj: setvar j
  assume climmulf.1: |- F/ k ph
  assume climmulf.2: |- F/_ k F
  assume climmulf.3: |- F/_ k G
  assume climmulf.4: |- F/_ k H
  assume climmulf.5: |- Z = ( ZZ>= ` M )
  assume climmulf.6: |- ( ph -> M e. ZZ )
  assume climmulf.7: |- ( ph -> F ~~> A )
  assume climmulf.8: |- ( ph -> H e. X )
  assume climmulf.9: |- ( ph -> G ~~> B )
  assume climmulf.10: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )
  assume climmulf.11: |- ( ( ph /\ k e. Z ) -> ( G ` k ) e. CC )
  assume climmulf.12: |- ( ( ph /\ k e. Z ) -> ( H ` k ) = ( ( F ` k ) x. ( G ` k ) ) )

  disjoint Z k
  disjoint j k
  disjoint j ph
  disjoint A j
  disjoint B j
  disjoint F j
  disjoint G j
  disjoint H j
  disjoint M j
  disjoint Z j
  assert |- ( ph -> H ~~> ( A x. B ) )

  proof
    wph
    cA
    cB
    vj
    cF
    cG
    cH
    cM
    cX
    cZ
    climmulf.5
    climmulf.6
    climmulf.7
    climmulf.8
    climmulf.9
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @0
    cF
    cfv
    #
    cc
    wcel
    #
    wi
    wph
    vj
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @5
    cF
    cfv
    #
    cc
    wcel
    #
    wi
    vk
    vj
    @7
    @9
    vk
    wph
    @6
    vk
    climmulf.1
    vk
    @5
    cZ
    vk
    @5
    nfcv
    #
    nfel1
    nfan
    #
    vk
    @8
    cc
    vk
    @5
    cF
    climmulf.2
    @10
    nffv
    #
    nfel1
    nfim
    @0
    @5
    wceq
    #
    @2
    @7
    @4
    @9
    @13
    @1
    @6
    wph
    @0
    @5
    cZ
    eleq1
    anbi2d
    #
    @13
    @3
    @8
    cc
    @0
    @5
    cF
    fveq2
    #
    eleq1d
    imbi12d
    climmulf.10
    chvar
    @2
    @0
    cG
    cfv
    #
    cc
    wcel
    #
    wi
    @7
    @5
    cG
    cfv
    #
    cc
    wcel
    #
    wi
    vk
    vj
    @7
    @19
    vk
    @11
    vk
    @18
    cc
    vk
    @5
    cG
    climmulf.3
    @10
    nffv
    #
    nfel1
    nfim
    @13
    @2
    @7
    @17
    @19
    @14
    @13
    @16
    @18
    cc
    @0
    @5
    cG
    fveq2
    #
    eleq1d
    imbi12d
    climmulf.11
    chvar
    @2
    @0
    cH
    cfv
    #
    @3
    @16
    cmul
    co
    #
    wceq
    #
    wi
    @7
    @5
    cH
    cfv
    #
    @8
    @18
    cmul
    co
    #
    wceq
    #
    wi
    vk
    vj
    @7
    @27
    vk
    @11
    vk
    @25
    @26
    vk
    @5
    cH
    climmulf.4
    @10
    nffv
    vk
    @8
    @18
    cmul
    @12
    vk
    cmul
    nfcv
    @20
    nfov
    nfeq
    nfim
    @13
    @2
    @7
    @24
    @27
    @14
    @13
    @22
    @25
    @23
    @26
    @0
    @5
    cH
    fveq2
    @13
    @3
    @8
    @16
    @18
    cmul
    @15
    @21
    oveq12d
    eqeq12d
    imbi12d
    climmulf.12
    chvar
    climmul
end
