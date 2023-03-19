include "caddc.mm"
include "cseq.mm"
include "cr.mm"
include "cv.mm"
include "serfre.mm"
include "ffvelrnda.mm"
include "wcel.mm"
include "wa.mm"
include "cuz.mm"
include "cfv.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "cfz.mm"
include "co.mm"
include "simpll.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "adantl.mm"
include "syl2anc.mm"
include "cle.mm"
include "wbr.mm"
include "serle.mm"
include "climle.mm"

theorem iserle
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  let cC: class C
  assume clim2ser.1: |- Z = ( ZZ>= ` M )
  assume iserle.2: |- ( ph -> M e. ZZ )
  assume iserle.4: |- ( ph -> seq M ( + , F ) ~~> A )
  assume iserle.5: |- ( ph -> seq M ( + , G ) ~~> B )
  assume iserle.6: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. RR )
  assume iserle.7: |- ( ( ph /\ k e. Z ) -> ( G ` k ) e. RR )
  assume iserle.8: |- ( ( ph /\ k e. Z ) -> ( F ` k ) <_ ( G ` k ) )

  disjoint A k
  disjoint B k
  disjoint F k
  disjoint M k
  disjoint G k
  disjoint k ph
  disjoint Z k
  disjoint j k
  disjoint A j
  disjoint B j
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
  disjoint C k
  disjoint C x
  disjoint G j
  disjoint j ph
  disjoint ph x
  disjoint ph y
  disjoint Z j
  disjoint Z x
  assert |- ( ph -> A <_ B )

  proof
    wph
    cA
    cB
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
    cZ
    clim2ser.1
    iserle.2
    iserle.4
    iserle.5
    wph
    cZ
    cr
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
    iserle.2
    iserle.6
    serfre
    ffvelrnda
    wph
    cZ
    cr
    @2
    @1
    wph
    vk
    cG
    cM
    cZ
    clim2ser.1
    iserle.2
    iserle.7
    serfre
    ffvelrnda
    wph
    @2
    cZ
    wcel
    #
    wa
    #
    vk
    cF
    cG
    cM
    @2
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
    @4
    vk
    cv
    #
    cM
    @2
    cfz
    co
    wcel
    #
    wa
    #
    wph
    @6
    cZ
    wcel
    #
    @6
    cF
    cfv
    #
    cr
    wcel
    wph
    @3
    @7
    simpll
    #
    @7
    @9
    @4
    @7
    @6
    @5
    cZ
    @6
    cM
    @2
    elfzuz
    clim2ser.1
    syl6eleqr
    adantl
    #
    iserle.6
    syl2anc
    @8
    wph
    @9
    @6
    cG
    cfv
    #
    cr
    wcel
    @11
    @12
    iserle.7
    syl2anc
    @8
    wph
    @9
    @10
    @13
    cle
    wbr
    @11
    @12
    iserle.8
    syl2anc
    serle
    climle
end
