include "caddc.mm"
include "cmin.mm"
include "cc.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "addcl.mm"
include "adantl.mm"
include "subcl.mm"
include "wceq.mm"
include "addsub4.mm"
include "eqcomd.mm"
include "seqcaopr2.mm"

theorem sersub
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume sersub.1: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume sersub.2: |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) e. CC )
  assume sersub.3: |- ( ( ph /\ k e. ( M ... N ) ) -> ( G ` k ) e. CC )
  assume sersub.4: |- ( ( ph /\ k e. ( M ... N ) ) -> ( H ` k ) = ( ( F ` k ) - ( G ` k ) ) )

  disjoint F k
  disjoint G k
  disjoint M k
  disjoint k ph
  disjoint H k
  disjoint N k
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint M w
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint H z
  disjoint N x
  disjoint N y
  disjoint N z
  assert |- ( ph -> ( seq M ( + , H ) ` N ) = ( ( seq M ( + , F ) ` N ) - ( seq M ( + , G ) ` N ) ) )

  proof
    wph
    vx
    vy
    vz
    vw
    caddc
    cmin
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
    vy
    cv
    #
    cc
    wcel
    wa
    #
    @0
    @1
    caddc
    co
    #
    cc
    wcel
    wph
    @0
    @1
    addcl
    adantl
    @2
    @0
    @1
    cmin
    co
    cc
    wcel
    wph
    @0
    @1
    subcl
    adantl
    @2
    vz
    cv
    #
    cc
    wcel
    vw
    cv
    #
    cc
    wcel
    wa
    wa
    #
    @0
    @4
    cmin
    co
    @1
    @5
    cmin
    co
    caddc
    co
    #
    @3
    @4
    @5
    caddc
    co
    cmin
    co
    #
    wceq
    wph
    @6
    @8
    @7
    @0
    @1
    @4
    @5
    addsub4
    eqcomd
    adantl
    sersub.1
    sersub.2
    sersub.3
    sersub.4
    seqcaopr2
end
