include "cfv.mm"
include "cuz.mm"
include "eqid.mm"
include "wcel.mm"
include "cz.mm"
include "syl6eleq.mm"
include "eluzelz.mm"
include "syl.mm"
include "cr.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "expcom.mm"
include "vtoclga.mm"
include "mpcom.mm"
include "uztrn2.mm"
include "sylan.mm"
include "impcom.mm"
include "syldan.mm"
include "wa.mm"
include "simpr.mm"
include "cfz.mm"
include "co.mm"
include "elfzuz.mm"
include "sylan2.mm"
include "adantlr.mm"
include "c1.mm"
include "cmin.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "monoord.mm"
include "climlec2.mm"

theorem climub
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vj: setvar j
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cG: class G
  assume clim2ser.1: |- Z = ( ZZ>= ` M )
  assume climub.2: |- ( ph -> N e. Z )
  assume climub.3: |- ( ph -> F ~~> A )
  assume climub.4: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. RR )
  assume climub.5: |- ( ( ph /\ k e. Z ) -> ( F ` k ) <_ ( F ` ( k + 1 ) ) )

  disjoint A k
  disjoint F k
  disjoint M k
  disjoint N k
  disjoint k ph
  disjoint Z k
  disjoint j k
  disjoint A j
  disjoint B j
  disjoint B k
  disjoint j x
  disjoint j y
  disjoint F j
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint M j
  disjoint M x
  disjoint M y
  disjoint N j
  disjoint N x
  disjoint N y
  disjoint C j
  disjoint C k
  disjoint C x
  disjoint G j
  disjoint G k
  disjoint j ph
  disjoint ph x
  disjoint ph y
  disjoint Z j
  disjoint Z x
  assert |- ( ph -> ( F ` N ) <_ A )

  proof
    wph
    cN
    cF
    cfv
    #
    cA
    vj
    cF
    cN
    cN
    cuz
    cfv
    #
    @1
    eqid
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    cN
    cz
    wcel
    wph
    cN
    cZ
    @2
    climub.2
    clim2ser.1
    syl6eleq
    cM
    cN
    eluzelz
    syl
    cN
    cZ
    wcel
    #
    wph
    @0
    cr
    wcel
    #
    climub.2
    wph
    vk
    cv
    #
    cF
    cfv
    #
    cr
    wcel
    #
    wi
    #
    wph
    @4
    wi
    vk
    cN
    cZ
    @5
    cN
    wceq
    #
    @7
    @4
    wph
    @9
    @6
    @0
    cr
    @5
    cN
    cF
    fveq2
    eleq1d
    imbi2d
    wph
    @5
    cZ
    wcel
    #
    @7
    climub.4
    expcom
    #
    vtoclga
    mpcom
    climub.3
    wph
    vj
    cv
    #
    @1
    wcel
    #
    @12
    cZ
    wcel
    #
    @12
    cF
    cfv
    #
    cr
    wcel
    #
    wph
    @3
    @13
    @14
    climub.2
    cM
    @12
    cN
    cZ
    clim2ser.1
    uztrn2
    sylan
    @14
    wph
    @16
    @8
    wph
    @16
    wi
    vk
    @12
    cZ
    @5
    @12
    wceq
    #
    @7
    @16
    wph
    @17
    @6
    @15
    cr
    @5
    @12
    cF
    fveq2
    eleq1d
    imbi2d
    @11
    vtoclga
    impcom
    syldan
    wph
    @13
    wa
    vk
    cF
    cN
    @12
    wph
    @13
    simpr
    wph
    @5
    cN
    @12
    cfz
    co
    wcel
    #
    @7
    @13
    @18
    wph
    @5
    @1
    wcel
    #
    @7
    @5
    cN
    @12
    elfzuz
    wph
    @19
    @10
    @7
    wph
    @3
    @19
    @10
    climub.2
    cM
    @5
    cN
    cZ
    clim2ser.1
    uztrn2
    sylan
    #
    climub.4
    syldan
    sylan2
    adantlr
    wph
    @5
    cN
    @12
    c1
    cmin
    co
    #
    cfz
    co
    wcel
    #
    @6
    @5
    c1
    caddc
    co
    cF
    cfv
    cle
    wbr
    #
    @13
    @22
    wph
    @19
    @23
    @5
    cN
    @21
    elfzuz
    wph
    @19
    @10
    @23
    @20
    climub.5
    syldan
    sylan2
    adantlr
    monoord
    climlec2
end
