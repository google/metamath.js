include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "cab.mm"
include "ciun.mm"
include "cfv.mm"
include "wfo.mm"
include "wf.mm"
include "fof.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "wceq.mm"
include "foelrn.mm"
include "sylan.mm"
include "wa.mm"
include "eleq2d.mm"
include "rexxfrd.mm"
include "bicomd.mm"
include "abbidv.mm"
include "df-iun.mm"
include "3eqtr4g.mm"

theorem iunrdx
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let vz: setvar z
  assume iunrdx.1: |- ( ph -> F : A -onto-> C )
  assume iunrdx.2: |- ( ( ph /\ y = ( F ` x ) ) -> D = B )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint F x
  disjoint F y
  disjoint ph x
  disjoint ph y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint D z
  disjoint ph z
  assert |- ( ph -> U_ x e. A B = U_ y e. C D )

  proof
    wph
    vz
    cv
    #
    cB
    wcel
    #
    vx
    cA
    wrex
    #
    vz
    cab
    @0
    cD
    wcel
    #
    vy
    cC
    wrex
    #
    vz
    cab
    vx
    cA
    cB
    ciun
    vy
    cC
    cD
    ciun
    wph
    @2
    @4
    vz
    wph
    @4
    @2
    wph
    @3
    @1
    vy
    vx
    vx
    cv
    #
    cF
    cfv
    #
    cC
    cA
    wph
    cA
    cC
    @5
    cF
    wph
    cA
    cC
    cF
    wfo
    #
    cA
    cC
    cF
    wf
    iunrdx.1
    cA
    cC
    cF
    fof
    syl
    ffvelrnda
    wph
    @7
    vy
    cv
    #
    cC
    wcel
    @8
    @6
    wceq
    #
    vx
    cA
    wrex
    iunrdx.1
    vx
    cA
    cC
    @8
    cF
    foelrn
    sylan
    wph
    @9
    wa
    cD
    cB
    @0
    iunrdx.2
    eleq2d
    rexxfrd
    bicomd
    abbidv
    vx
    vz
    cA
    cB
    df-iun
    vy
    vz
    cC
    cD
    df-iun
    3eqtr4g
end
