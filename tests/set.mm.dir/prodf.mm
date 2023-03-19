include "cmul.mm"
include "cc.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "mulcl.mm"
include "adantl.mm"
include "seqf.mm"

theorem prodf
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  assume prodf.1: |- Z = ( ZZ>= ` M )
  assume prodf.2: |- ( ph -> M e. ZZ )
  assume prodf.3: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )

  disjoint F k
  disjoint k ph
  disjoint M k
  disjoint Z k
  disjoint F x
  disjoint k x
  disjoint ph x
  disjoint M x
  assert |- ( ph -> seq M ( x. , F ) : Z --> CC )

  proof
    wph
    vk
    vx
    cmul
    cc
    cF
    cM
    cZ
    prodf.1
    prodf.2
    prodf.3
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
    cmul
    co
    cc
    wcel
    wph
    @0
    @1
    mulcl
    adantl
    seqf
end
