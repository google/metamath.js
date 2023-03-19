include "c1.mm"
include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "wcel.mm"
include "uzid.mm"
include "syl.mm"
include "syl6eleqr.mm"
include "cv.mm"
include "wa.mm"
include "cabs.mm"
include "cr.mm"
include "abscld.mm"
include "eqeltrd.mm"
include "1red.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "eleq2i.mm"
include "wceq.mm"
include "eqcomd.mm"
include "eqle.mm"
include "syl2anc.mm"
include "recnd.mm"
include "mulid2d.mm"
include "breqtrrd.mm"
include "sylan2br.mm"
include "cvgcmpce.mm"

theorem abscvgcvg
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  assume abscvgcvg.1: |- Z = ( ZZ>= ` M )
  assume abscvgcvg.2: |- ( ph -> M e. ZZ )
  assume abscvgcvg.3: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = ( abs ` ( G ` k ) ) )
  assume abscvgcvg.4: |- ( ( ph /\ k e. Z ) -> ( G ` k ) e. CC )
  assume abscvgcvg.5: |- ( ph -> seq M ( + , F ) e. dom ~~> )

  disjoint F k
  disjoint G k
  disjoint M k
  disjoint k ph
  disjoint Z k
  assert |- ( ph -> seq M ( + , G ) e. dom ~~> )

  proof
    wph
    c1
    vk
    cF
    cG
    cM
    cM
    cZ
    abscvgcvg.1
    wph
    cM
    cM
    cuz
    cfv
    #
    cZ
    wph
    cM
    cz
    wcel
    cM
    @0
    wcel
    abscvgcvg.2
    cM
    uzid
    syl
    abscvgcvg.1
    syl6eleqr
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @1
    cF
    cfv
    #
    @1
    cG
    cfv
    #
    cabs
    cfv
    #
    cr
    abscvgcvg.3
    @3
    @5
    abscvgcvg.4
    abscld
    #
    eqeltrd
    #
    abscvgcvg.4
    abscvgcvg.5
    wph
    1red
    @1
    @0
    wcel
    wph
    @2
    @6
    c1
    @4
    cmul
    co
    #
    cle
    wbr
    cZ
    @0
    @1
    abscvgcvg.1
    eleq2i
    @3
    @6
    @4
    @9
    cle
    @3
    @6
    cr
    wcel
    @6
    @4
    wceq
    @6
    @4
    cle
    wbr
    @7
    @3
    @4
    @6
    abscvgcvg.3
    eqcomd
    @6
    @4
    eqle
    syl2anc
    @3
    @4
    @3
    @4
    @8
    recnd
    mulid2d
    breqtrrd
    sylan2br
    cvgcmpce
end
