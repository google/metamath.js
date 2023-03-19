include "caddc.mm"
include "cr.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "readdcl.mm"
include "adantl.mm"
include "seqf.mm"

theorem serfre
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  assume serf.1: |- Z = ( ZZ>= ` M )
  assume serf.2: |- ( ph -> M e. ZZ )
  assume serfre.3: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. RR )

  disjoint F k
  disjoint M k
  disjoint k ph
  disjoint Z k
  disjoint k x
  disjoint F x
  disjoint M x
  disjoint ph x
  assert |- ( ph -> seq M ( + , F ) : Z --> RR )

  proof
    wph
    vk
    vx
    caddc
    cr
    cF
    cM
    cZ
    serf.1
    serf.2
    serfre.3
    vk
    cv
    #
    cr
    wcel
    vx
    cv
    #
    cr
    wcel
    wa
    @0
    @1
    caddc
    co
    cr
    wcel
    wph
    @0
    @1
    readdcl
    adantl
    seqf
end
