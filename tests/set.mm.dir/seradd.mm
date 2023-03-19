include "caddc.mm"
include "cc.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "addcl.mm"
include "adantl.mm"
include "wceq.mm"
include "addcom.mm"
include "w3a.mm"
include "addass.mm"
include "seqcaopr.mm"

theorem seradd
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
  assume seradd.1: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume seradd.2: |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) e. CC )
  assume seradd.3: |- ( ( ph /\ k e. ( M ... N ) ) -> ( G ` k ) e. CC )
  assume seradd.4: |- ( ( ph /\ k e. ( M ... N ) ) -> ( H ` k ) = ( ( F ` k ) + ( G ` k ) ) )

  disjoint F k
  disjoint G k
  disjoint M k
  disjoint k ph
  disjoint H k
  disjoint N k
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint H z
  disjoint N x
  disjoint N y
  disjoint N z
  assert |- ( ph -> ( seq M ( + , H ) ` N ) = ( ( seq M ( + , F ) ` N ) + ( seq M ( + , G ) ` N ) ) )

  proof
    wph
    vx
    vy
    vz
    caddc
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
    caddc
    co
    #
    cc
    wcel
    wph
    @0
    @2
    addcl
    adantl
    @4
    @5
    @2
    @0
    caddc
    co
    wceq
    wph
    @0
    @2
    addcom
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
    caddc
    co
    @0
    @2
    @6
    caddc
    co
    caddc
    co
    wceq
    wph
    @0
    @2
    @6
    addass
    adantl
    seradd.1
    seradd.2
    seradd.3
    seradd.4
    seqcaopr
end
