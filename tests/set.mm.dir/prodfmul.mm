include "cmul.mm"
include "cc.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "mulcl.mm"
include "adantl.mm"
include "wceq.mm"
include "mulcom.mm"
include "w3a.mm"
include "mulass.mm"
include "seqcaopr.mm"

theorem prodfmul
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume prodfmul.1: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume prodfmul.2: |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) e. CC )
  assume prodfmul.3: |- ( ( ph /\ k e. ( M ... N ) ) -> ( G ` k ) e. CC )
  assume prodfmul.4: |- ( ( ph /\ k e. ( M ... N ) ) -> ( H ` k ) = ( ( F ` k ) x. ( G ` k ) ) )

  disjoint F k
  disjoint G k
  disjoint H k
  disjoint k ph
  disjoint M k
  disjoint N k
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( ph -> ( seq M ( x. , H ) ` N ) = ( ( seq M ( x. , F ) ` N ) x. ( seq M ( x. , G ) ` N ) ) )

  proof
    wph
    vx
    vy
    vz
    cmul
    cc
    vk
    cF
    cG
    cH
    cM
    cN
    vx
    cv
    #
    cc
    wcel
    #
    vy
    cv
    #
    cc
    wcel
    #
    wa
    #
    @0
    @2
    cmul
    co
    #
    cc
    wcel
    wph
    @0
    @2
    mulcl
    adantl
    @4
    @5
    @2
    @0
    cmul
    co
    wceq
    wph
    @0
    @2
    mulcom
    adantl
    @1
    @3
    vz
    cv
    #
    cc
    wcel
    w3a
    @5
    @6
    cmul
    co
    @0
    @2
    @6
    cmul
    co
    cmul
    co
    wceq
    wph
    @0
    @2
    @6
    mulass
    adantl
    prodfmul.1
    prodfmul.2
    prodfmul.3
    prodfmul.4
    seqcaopr
end
