include "csu.mm"
include "caddc.mm"
include "cseq.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "recnd.mm"
include "isumclim2.mm"
include "cr.mm"
include "cfv.mm"
include "eqeltrd.mm"
include "serfre.mm"
include "ffvelrnda.mm"
include "climrecl.mm"

theorem isumrecl
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  assume isumrecl.1: |- Z = ( ZZ>= ` M )
  assume isumrecl.2: |- ( ph -> M e. ZZ )
  assume isumrecl.3: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = A )
  assume isumrecl.4: |- ( ( ph /\ k e. Z ) -> A e. RR )
  assume isumrecl.5: |- ( ph -> seq M ( + , F ) e. dom ~~> )

  disjoint F k
  disjoint M k
  disjoint k ph
  disjoint Z k
  disjoint A j
  disjoint j k
  disjoint F j
  disjoint M j
  disjoint j ph
  disjoint Z j
  assert |- ( ph -> sum_ k e. Z A e. RR )

  proof
    wph
    cZ
    cA
    vk
    csu
    vj
    caddc
    cF
    cM
    cseq
    #
    cM
    cZ
    isumrecl.1
    isumrecl.2
    wph
    cA
    vk
    cF
    cM
    cZ
    isumrecl.1
    isumrecl.2
    isumrecl.3
    wph
    vk
    cv
    #
    cZ
    wcel
    wa
    #
    cA
    isumrecl.4
    recnd
    isumrecl.5
    isumclim2
    wph
    cZ
    cr
    vj
    cv
    @0
    wph
    vk
    cF
    cM
    cZ
    isumrecl.1
    isumrecl.2
    @2
    @1
    cF
    cfv
    cA
    cr
    isumrecl.3
    isumrecl.4
    eqeltrd
    serfre
    ffvelrnda
    climrecl
end
