include "cmpt.mm"
include "ccom.mm"
include "cfv.mm"
include "crli.mm"
include "cv.mm"
include "eqidd.mm"
include "cc.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "eqid.mm"
include "fmptd.mm"
include "rlimcn1.mm"
include "eqbrtrrd.mm"

theorem rlimcn1b
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cF: class F
  let cX: class X
  assume rlimcn1b.1: |- ( ( ph /\ k e. A ) -> B e. X )
  assume rlimcn1b.2: |- ( ph -> C e. X )
  assume rlimcn1b.3: |- ( ph -> ( k e. A |-> B ) ~~>r C )
  assume rlimcn1b.4: |- ( ph -> F : X --> CC )
  assume rlimcn1b.5: |- ( ( ph /\ x e. RR+ ) -> E. y e. RR+ A. z e. X ( ( abs ` ( z - C ) ) < y -> ( abs ` ( ( F ` z ) - ( F ` C ) ) ) < x ) )

  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint F k
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint X k
  disjoint X z
  disjoint k ph
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( k e. A |-> ( F ` B ) ) ~~>r ( F ` C ) )

  proof
    wph
    cF
    vk
    cA
    cB
    cmpt
    #
    ccom
    vk
    cA
    cB
    cF
    cfv
    #
    cmpt
    cC
    cF
    cfv
    crli
    wph
    vk
    vz
    cA
    cX
    cB
    vz
    cv
    #
    cF
    cfv
    @1
    @0
    cF
    rlimcn1b.1
    wph
    @0
    eqidd
    wph
    vz
    cX
    cc
    cF
    rlimcn1b.4
    feqmptd
    @2
    cB
    cF
    fveq2
    fmptco
    wph
    vx
    vy
    vz
    cA
    cC
    cF
    @0
    cX
    wph
    vk
    cA
    cB
    cX
    @0
    rlimcn1b.1
    @0
    eqid
    fmptd
    rlimcn1b.2
    rlimcn1b.3
    rlimcn1b.4
    rlimcn1b.5
    rlimcn1
    eqbrtrrd
end
