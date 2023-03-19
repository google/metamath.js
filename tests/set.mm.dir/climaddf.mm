include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cc.mm"
include "wi.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfel1.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "caddc.mm"
include "co.mm"
include "nfov.mm"
include "nfeq.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "climadd.mm"

theorem climaddf
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
  assume climaddf.1: |- F/ k ph
  assume climaddf.2: |- F/_ k F
  assume climaddf.3: |- F/_ k G
  assume climaddf.4: |- F/_ k H
  assume climaddf.5: |- Z = ( ZZ>= ` M )
  assume climaddf.6: |- ( ph -> M e. ZZ )
  assume climaddf.7: |- ( ph -> F ~~> A )
  assume climaddf.8: |- ( ph -> H e. X )
  assume climaddf.9: |- ( ph -> G ~~> B )
  assume climaddf.10: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )
  assume climaddf.11: |- ( ( ph /\ k e. Z ) -> ( G ` k ) e. CC )
  assume climaddf.12: |- ( ( ph /\ k e. Z ) -> ( H ` k ) = ( ( F ` k ) + ( G ` k ) ) )

  disjoint Z k
  disjoint A j
  disjoint B j
  disjoint F j
  disjoint G j
  disjoint H j
  disjoint M j
  disjoint Z j
  disjoint j k
  disjoint j ph
  assert |- ( ph -> H ~~> ( A + B ) )

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
    climaddf.5
    climaddf.6
    climaddf.7
    climaddf.8
    climaddf.9
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
    climaddf.1
    @6
    vk
    nfv
    nfan
    #
    vk
    @8
    cc
    vk
    @5
    cF
    climaddf.2
    vk
    @5
    nfcv
    #
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
    climaddf.10
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
    @10
    vk
    @18
    cc
    vk
    @5
    cG
    climaddf.3
    @11
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
    climaddf.11
    chvar
    @2
    @0
    cH
    cfv
    #
    @3
    @16
    caddc
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
    caddc
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
    @10
    vk
    @25
    @26
    vk
    @5
    cH
    climaddf.4
    @11
    nffv
    vk
    @8
    @18
    caddc
    @12
    vk
    caddc
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
    caddc
    @15
    @21
    oveq12d
    eqeq12d
    imbi12d
    climaddf.12
    chvar
    climadd
end
