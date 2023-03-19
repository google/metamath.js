include "caddc.mm"
include "cseq.mm"
include "cvv.mm"
include "wcel.mm"
include "seqex.mm"
include "a1i.mm"
include "cc.mm"
include "cv.mm"
include "serf.mm"
include "ffvelrnda.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "addcl.mm"
include "adantl.mm"
include "wceq.mm"
include "adantr.mm"
include "adddi.mm"
include "3expb.mm"
include "sylan.mm"
include "cuz.mm"
include "cfv.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "cfz.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "sylan2.mm"
include "adantlr.mm"
include "seqdistr.mm"
include "climmulc2.mm"

theorem isermulc2
  let wph: wff ph
  let cA: class A
  let cC: class C
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  assume clim2ser.1: |- Z = ( ZZ>= ` M )
  assume isermulc2.2: |- ( ph -> M e. ZZ )
  assume isermulc2.4: |- ( ph -> C e. CC )
  assume isermulc2.5: |- ( ph -> seq M ( + , F ) ~~> A )
  assume isermulc2.6: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )
  assume isermulc2.7: |- ( ( ph /\ k e. Z ) -> ( G ` k ) = ( C x. ( F ` k ) ) )

  disjoint A k
  disjoint F k
  disjoint M k
  disjoint C k
  disjoint G k
  disjoint k ph
  disjoint Z k
  disjoint j k
  disjoint A j
  disjoint B j
  disjoint B k
  disjoint j x
  disjoint j y
  disjoint F j
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint M j
  disjoint M x
  disjoint M y
  disjoint N j
  disjoint N k
  disjoint N x
  disjoint N y
  disjoint C j
  disjoint C x
  disjoint G j
  disjoint j ph
  disjoint ph x
  disjoint ph y
  disjoint Z j
  disjoint Z x
  assert |- ( ph -> seq M ( + , G ) ~~> ( C x. A ) )

  proof
    wph
    cA
    cC
    vj
    caddc
    cF
    cM
    cseq
    #
    caddc
    cG
    cM
    cseq
    #
    cM
    cvv
    cZ
    clim2ser.1
    isermulc2.2
    isermulc2.5
    isermulc2.4
    @1
    cvv
    wcel
    wph
    caddc
    cG
    cM
    seqex
    a1i
    wph
    cZ
    cc
    vj
    cv
    #
    @0
    wph
    vk
    cF
    cM
    cZ
    clim2ser.1
    isermulc2.2
    isermulc2.6
    serf
    ffvelrnda
    wph
    @2
    cZ
    wcel
    #
    wa
    #
    vk
    vx
    cC
    caddc
    cc
    cmul
    cG
    cF
    cM
    @2
    vk
    cv
    #
    cc
    wcel
    #
    vx
    cv
    #
    cc
    wcel
    #
    wa
    #
    @5
    @7
    caddc
    co
    #
    cc
    wcel
    @4
    @5
    @7
    addcl
    adantl
    @4
    cC
    cc
    wcel
    #
    @9
    cC
    @10
    cmul
    co
    cC
    @5
    cmul
    co
    cC
    @7
    cmul
    co
    caddc
    co
    wceq
    #
    wph
    @11
    @3
    isermulc2.4
    adantr
    @11
    @6
    @8
    @12
    cC
    @5
    @7
    adddi
    3expb
    sylan
    @4
    @2
    cZ
    cM
    cuz
    cfv
    #
    wph
    @3
    simpr
    clim2ser.1
    syl6eleq
    wph
    @5
    cM
    @2
    cfz
    co
    wcel
    #
    @5
    cF
    cfv
    #
    cc
    wcel
    #
    @3
    @14
    wph
    @5
    cZ
    wcel
    #
    @16
    @14
    @5
    @13
    cZ
    @5
    cM
    @2
    elfzuz
    clim2ser.1
    syl6eleqr
    #
    isermulc2.6
    sylan2
    adantlr
    wph
    @14
    @5
    cG
    cfv
    cC
    @15
    cmul
    co
    wceq
    #
    @3
    @14
    wph
    @17
    @19
    @18
    isermulc2.7
    sylan2
    adantlr
    seqdistr
    climmulc2
end
