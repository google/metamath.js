include "caddc.mm"
include "cc.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "addcl.mm"
include "adantl.mm"
include "seqf.mm"

theorem serf
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  assume serf.1: |- Z = ( ZZ>= ` M )
  assume serf.2: |- ( ph -> M e. ZZ )
  assume serf.3: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )

  disjoint F k
  disjoint M k
  disjoint k ph
  disjoint Z k
  disjoint k x
  disjoint F x
  disjoint M x
  disjoint ph x
  assert |- ( ph -> seq M ( + , F ) : Z --> CC )

  proof
    wph
    vk
    vx
    caddc
    cc
    cF
    cM
    cZ
    serf.1
    serf.2
    serf.3
    vk
    cv
    #
    cc
    wcel
    vx
    cv
    #
    cc
    wcel
    wa
    @0
    @1
    caddc
    co
    cc
    wcel
    wph
    @0
    @1
    addcl
    adantl
    seqf
end
