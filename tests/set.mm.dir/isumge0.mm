include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "cle.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "wcel.mm"
include "wa.mm"
include "recnd.mm"
include "isumclim2.mm"
include "fveq2.mm"
include "cbvsumv.mm"
include "sumeq2dv.mm"
include "syl5eq.mm"
include "breqtrrd.mm"
include "cr.mm"
include "eqeltrd.mm"
include "iserge0.mm"
include "breqtrd.mm"

theorem isumge0
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
  assume isumge0.6: |- ( ( ph /\ k e. Z ) -> 0 <_ A )

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
  assert |- ( ph -> 0 <_ sum_ k e. Z A )

  proof
    wph
    cc0
    cZ
    vj
    cv
    #
    cF
    cfv
    #
    vj
    csu
    #
    cZ
    cA
    vk
    csu
    #
    cle
    wph
    @2
    vk
    cF
    cM
    cZ
    isumrecl.1
    isumrecl.2
    wph
    caddc
    cF
    cM
    cseq
    @3
    @2
    cli
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
    @2
    cZ
    @4
    cF
    cfv
    #
    vk
    csu
    @3
    cZ
    @1
    @6
    vj
    vk
    @0
    @4
    cF
    fveq2
    cbvsumv
    wph
    cZ
    @6
    cA
    vk
    isumrecl.3
    sumeq2dv
    syl5eq
    #
    breqtrrd
    @5
    @6
    cA
    cr
    isumrecl.3
    isumrecl.4
    eqeltrd
    @5
    cc0
    cA
    @6
    cle
    isumge0.6
    isumrecl.3
    breqtrrd
    iserge0
    @7
    breqtrd
end
