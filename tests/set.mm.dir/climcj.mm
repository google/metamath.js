include "ccj.mm"
include "cjf.mm"
include "cjcn2.mm"
include "climcn1lem.mm"

theorem climcj
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cW: class W
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cH: class H
  assume climcn1lem.1: |- Z = ( ZZ>= ` M )
  assume climcn1lem.2: |- ( ph -> F ~~> A )
  assume climcn1lem.4: |- ( ph -> G e. W )
  assume climcn1lem.5: |- ( ph -> M e. ZZ )
  assume climcn1lem.6: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )
  assume climcj.7: |- ( ( ph /\ k e. Z ) -> ( G ` k ) = ( * ` ( F ` k ) ) )

  disjoint A k
  disjoint F k
  disjoint G k
  disjoint k ph
  disjoint Z k
  disjoint M k
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F y
  disjoint F z
  disjoint G x
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint Z y
  disjoint H k
  disjoint H x
  disjoint H y
  disjoint H z
  assert |- ( ph -> G ~~> ( * ` A ) )

  proof
    wph
    vx
    vy
    vz
    cA
    vk
    cF
    cG
    ccj
    cM
    cW
    cZ
    climcn1lem.1
    climcn1lem.2
    climcn1lem.4
    climcn1lem.5
    climcn1lem.6
    cjf
    vx
    vy
    vz
    cA
    cjcn2
    climcj.7
    climcn1lem
end
