include "cneg.mm"
include "csu.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "mulm1d.mm"
include "eqcomd.mm"
include "sumeq2dv.mm"
include "1cnd.mm"
include "negcld.mm"
include "isummulc2.mm"
include "3eqtr2d.mm"

theorem isumneg
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  assume isumneg.1: |- Z = ( ZZ>= ` M )
  assume isumneg.2: |- ( ph -> M e. ZZ )
  assume isumneg.3: |- ( ph -> sum_ k e. Z A e. CC )
  assume isumneg.4: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = A )
  assume isumneg.5: |- ( ( ph /\ k e. Z ) -> A e. CC )
  assume isumneg.6: |- ( ph -> seq M ( + , F ) e. dom ~~> )

  disjoint k ph
  disjoint F k
  disjoint M k
  disjoint Z k
  assert |- ( ph -> sum_ k e. Z -u A = -u sum_ k e. Z A )

  proof
    wph
    cZ
    cA
    cneg
    #
    vk
    csu
    cZ
    c1
    cneg
    #
    cA
    cmul
    co
    #
    vk
    csu
    @1
    cZ
    cA
    vk
    csu
    #
    cmul
    co
    @3
    cneg
    wph
    cZ
    @0
    @2
    vk
    wph
    vk
    cv
    cZ
    wcel
    wa
    #
    @2
    @0
    @4
    cA
    isumneg.5
    mulm1d
    eqcomd
    sumeq2dv
    wph
    cA
    @1
    vk
    cF
    cM
    cZ
    isumneg.1
    isumneg.2
    isumneg.4
    isumneg.5
    isumneg.6
    wph
    c1
    wph
    1cnd
    negcld
    isummulc2
    wph
    @3
    isumneg.3
    mulm1d
    3eqtr2d
end
