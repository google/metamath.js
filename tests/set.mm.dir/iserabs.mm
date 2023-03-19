include "cabs.mm"
include "cfv.mm"
include "cv.mm"
include "caddc.mm"
include "cseq.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "cuz.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "a1i.mm"
include "cc.mm"
include "serf.mm"
include "ffvelrnda.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eqid.mm"
include "fvmpt.mm"
include "adantl.mm"
include "climabs.mm"
include "wa.mm"
include "cr.mm"
include "abscld.mm"
include "eqeltrd.mm"
include "serfre.mm"
include "cle.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "cfz.mm"
include "co.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "sylan2.mm"
include "adantlr.mm"
include "seqabs.mm"
include "eqbrtrd.mm"
include "climle.mm"

theorem iserabs
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vm: setvar m
  let vn: setvar n
  assume iserabs.1: |- Z = ( ZZ>= ` M )
  assume iserabs.2: |- ( ph -> seq M ( + , F ) ~~> A )
  assume iserabs.3: |- ( ph -> seq M ( + , G ) ~~> B )
  assume iserabs.5: |- ( ph -> M e. ZZ )
  assume iserabs.6: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )
  assume iserabs.7: |- ( ( ph /\ k e. Z ) -> ( G ` k ) = ( abs ` ( F ` k ) ) )

  disjoint F k
  disjoint G k
  disjoint M k
  disjoint k ph
  disjoint Z k
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint F m
  disjoint F n
  disjoint G n
  disjoint M m
  disjoint M n
  disjoint n ph
  disjoint Z m
  disjoint Z n
  disjoint A n
  disjoint B n
  assert |- ( ph -> ( abs ` A ) <_ B )

  proof
    wph
    cA
    cabs
    cfv
    cB
    vn
    vm
    cZ
    vm
    cv
    #
    caddc
    cF
    cM
    cseq
    #
    cfv
    #
    cabs
    cfv
    #
    cmpt
    #
    caddc
    cG
    cM
    cseq
    #
    cM
    cZ
    iserabs.1
    iserabs.5
    wph
    cA
    vn
    @1
    @4
    cM
    cvv
    cZ
    iserabs.1
    iserabs.2
    @4
    cvv
    wcel
    wph
    vm
    cZ
    @3
    cZ
    cM
    cuz
    cfv
    #
    cvv
    iserabs.1
    cM
    cuz
    fvex
    eqeltri
    mptex
    a1i
    iserabs.5
    wph
    cZ
    cc
    vn
    cv
    #
    @1
    wph
    vk
    cF
    cM
    cZ
    iserabs.1
    iserabs.5
    iserabs.6
    serf
    ffvelrnda
    #
    @7
    cZ
    wcel
    #
    @7
    @4
    cfv
    #
    @7
    @1
    cfv
    #
    cabs
    cfv
    #
    wceq
    wph
    vm
    @7
    @3
    @12
    cZ
    @4
    @0
    @7
    wceq
    @2
    @11
    cabs
    @0
    @7
    @1
    fveq2
    fveq2d
    @4
    eqid
    @11
    cabs
    fvex
    fvmpt
    adantl
    #
    climabs
    iserabs.3
    wph
    @9
    wa
    #
    @10
    @12
    cr
    @13
    @14
    @11
    @8
    abscld
    eqeltrd
    wph
    cZ
    cr
    @7
    @5
    wph
    vk
    cG
    cM
    cZ
    iserabs.1
    iserabs.5
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @15
    cG
    cfv
    #
    @15
    cF
    cfv
    #
    cabs
    cfv
    #
    cr
    iserabs.7
    @17
    @19
    iserabs.6
    abscld
    eqeltrd
    serfre
    ffvelrnda
    @14
    @10
    @12
    @7
    @5
    cfv
    cle
    @13
    @14
    vk
    cF
    cG
    cM
    @7
    @14
    @7
    cZ
    @6
    wph
    @9
    simpr
    iserabs.1
    syl6eleq
    wph
    @15
    cM
    @7
    cfz
    co
    wcel
    #
    @19
    cc
    wcel
    #
    @9
    @21
    wph
    @16
    @22
    @21
    @15
    @6
    cZ
    @15
    cM
    @7
    elfzuz
    iserabs.1
    syl6eleqr
    #
    iserabs.6
    sylan2
    adantlr
    wph
    @21
    @18
    @20
    wceq
    #
    @9
    @21
    wph
    @16
    @24
    @23
    iserabs.7
    sylan2
    adantlr
    seqabs
    eqbrtrd
    climle
end
