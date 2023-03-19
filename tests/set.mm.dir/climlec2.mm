include "cz.mm"
include "csn.mm"
include "cxp.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cli.mm"
include "wbr.mm"
include "recnd.mm"
include "0z.mm"
include "uzssz.mm"
include "zex.mm"
include "climconst2.mm"
include "sylancl.mm"
include "cv.mm"
include "wa.mm"
include "cfv.mm"
include "cr.mm"
include "wceq.mm"
include "cuz.mm"
include "eluzelz.mm"
include "eleq2s.mm"
include "fvconst2g.mm"
include "syl2an.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "cle.mm"
include "eqbrtrd.mm"
include "climle.mm"

theorem climlec2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  let cC: class C
  let cG: class G
  assume clim2ser.1: |- Z = ( ZZ>= ` M )
  assume climlec2.2: |- ( ph -> M e. ZZ )
  assume climlec2.3: |- ( ph -> A e. RR )
  assume climlec2.4: |- ( ph -> F ~~> B )
  assume climlec2.5: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. RR )
  assume climlec2.6: |- ( ( ph /\ k e. Z ) -> A <_ ( F ` k ) )

  disjoint A k
  disjoint B k
  disjoint F k
  disjoint M k
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
  disjoint G k
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
    vk
    cz
    cA
    csn
    cxp
    #
    cF
    cM
    cZ
    clim2ser.1
    climlec2.2
    wph
    cA
    cc
    wcel
    cc0
    cz
    wcel
    @0
    cA
    cli
    wbr
    wph
    cA
    climlec2.3
    recnd
    0z
    cA
    cc0
    cz
    cc0
    uzssz
    zex
    climconst2
    sylancl
    climlec2.4
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @1
    @0
    cfv
    #
    cA
    cr
    wph
    cA
    cr
    wcel
    #
    @1
    cz
    wcel
    #
    @4
    cA
    wceq
    @2
    climlec2.3
    @6
    @1
    cM
    cuz
    cfv
    cZ
    cM
    @1
    eluzelz
    clim2ser.1
    eleq2s
    cz
    cA
    @1
    cr
    fvconst2g
    syl2an
    #
    wph
    @5
    @2
    climlec2.3
    adantr
    eqeltrd
    climlec2.5
    @3
    @4
    cA
    @1
    cF
    cfv
    cle
    @7
    climlec2.6
    eqbrtrd
    climle
end
