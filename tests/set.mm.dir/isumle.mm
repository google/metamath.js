include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "cfv.mm"
include "csu.mm"
include "cle.mm"
include "cdm.mm"
include "wcel.mm"
include "wbr.mm"
include "climdm.mm"
include "sylib.mm"
include "cv.mm"
include "wa.mm"
include "cr.mm"
include "eqeltrd.mm"
include "3brtr4d.mm"
include "iserle.mm"
include "recnd.mm"
include "isum.mm"

theorem isumle
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  assume isumle.1: |- Z = ( ZZ>= ` M )
  assume isumle.2: |- ( ph -> M e. ZZ )
  assume isumle.3: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = A )
  assume isumle.4: |- ( ( ph /\ k e. Z ) -> A e. RR )
  assume isumle.5: |- ( ( ph /\ k e. Z ) -> ( G ` k ) = B )
  assume isumle.6: |- ( ( ph /\ k e. Z ) -> B e. RR )
  assume isumle.7: |- ( ( ph /\ k e. Z ) -> A <_ B )
  assume isumle.8: |- ( ph -> seq M ( + , F ) e. dom ~~> )
  assume isumle.9: |- ( ph -> seq M ( + , G ) e. dom ~~> )

  disjoint F k
  disjoint G k
  disjoint M k
  disjoint k ph
  disjoint Z k
  assert |- ( ph -> sum_ k e. Z A <_ sum_ k e. Z B )

  proof
    wph
    caddc
    cF
    cM
    cseq
    #
    cli
    cfv
    #
    caddc
    cG
    cM
    cseq
    #
    cli
    cfv
    #
    cZ
    cA
    vk
    csu
    cZ
    cB
    vk
    csu
    cle
    wph
    @1
    @3
    vk
    cF
    cG
    cM
    cZ
    isumle.1
    isumle.2
    wph
    @0
    cli
    cdm
    #
    wcel
    @0
    @1
    cli
    wbr
    isumle.8
    @0
    climdm
    sylib
    wph
    @2
    @4
    wcel
    @2
    @3
    cli
    wbr
    isumle.9
    @2
    climdm
    sylib
    wph
    vk
    cv
    #
    cZ
    wcel
    wa
    #
    @5
    cF
    cfv
    #
    cA
    cr
    isumle.3
    isumle.4
    eqeltrd
    @6
    @5
    cG
    cfv
    #
    cB
    cr
    isumle.5
    isumle.6
    eqeltrd
    @6
    cA
    cB
    @7
    @8
    cle
    isumle.7
    isumle.3
    isumle.5
    3brtr4d
    iserle
    wph
    cA
    vk
    cF
    cM
    cZ
    isumle.1
    isumle.2
    isumle.3
    @6
    cA
    isumle.4
    recnd
    isum
    wph
    cB
    vk
    cG
    cM
    cZ
    isumle.1
    isumle.2
    isumle.5
    @6
    cB
    isumle.6
    recnd
    isum
    3brtr4d
end
