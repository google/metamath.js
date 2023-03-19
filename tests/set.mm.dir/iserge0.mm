include "cc0.mm"
include "cuz.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cz.mm"
include "wcel.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "serclim0.mm"
include "syl.mm"
include "cv.mm"
include "wa.mm"
include "cr.mm"
include "wceq.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "c0ex.mm"
include "fvconst2.mm"
include "0re.mm"
include "syl6eqel.mm"
include "cle.mm"
include "eqbrtrd.mm"
include "iserle.mm"

theorem iserge0
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  let cC: class C
  let cG: class G
  assume clim2ser.1: |- Z = ( ZZ>= ` M )
  assume iserge0.2: |- ( ph -> M e. ZZ )
  assume iserge0.3: |- ( ph -> seq M ( + , F ) ~~> A )
  assume iserge0.4: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. RR )
  assume iserge0.5: |- ( ( ph /\ k e. Z ) -> 0 <_ ( F ` k ) )

  disjoint A k
  disjoint F k
  disjoint M k
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
  disjoint C k
  disjoint C x
  disjoint G j
  disjoint G k
  disjoint j ph
  disjoint ph x
  disjoint ph y
  disjoint Z j
  disjoint Z x
  assert |- ( ph -> 0 <_ A )

  proof
    wph
    cc0
    cA
    vk
    cM
    cuz
    cfv
    #
    cc0
    csn
    cxp
    #
    cF
    cM
    cZ
    clim2ser.1
    iserge0.2
    wph
    cM
    cz
    wcel
    caddc
    @1
    cM
    cseq
    cc0
    cli
    wbr
    iserge0.2
    cM
    serclim0
    syl
    iserge0.3
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @2
    @1
    cfv
    #
    cc0
    cr
    @4
    @2
    @0
    wcel
    @5
    cc0
    wceq
    @4
    @2
    cZ
    @0
    wph
    @3
    simpr
    clim2ser.1
    syl6eleq
    @0
    cc0
    @2
    c0ex
    fvconst2
    syl
    #
    0re
    syl6eqel
    iserge0.4
    @4
    @5
    cc0
    @2
    cF
    cfv
    cle
    @6
    iserge0.5
    eqbrtrd
    iserle
end
