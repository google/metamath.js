include "caddc.mm"
include "cseq.mm"
include "cr.mm"
include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "syl6eleq.mm"
include "eluzel2.mm"
include "syl.mm"
include "serfre.mm"
include "ffvelrnda.mm"
include "wa.mm"
include "c1.mm"
include "co.mm"
include "cle.mm"
include "cc0.mm"
include "wbr.mm"
include "peano2uzs.mm"
include "wi.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq2d.mm"
include "imbi2d.mm"
include "expcom.mm"
include "vtoclga.mm"
include "impcom.mm"
include "sylan2.mm"
include "eleq1d.mm"
include "addge01d.mm"
include "mpbid.mm"
include "simpr.mm"
include "seqp1.mm"
include "breqtrrd.mm"
include "climub.mm"

theorem climserle
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
  assume climserle.2: |- ( ph -> N e. Z )
  assume climserle.3: |- ( ph -> seq M ( + , F ) ~~> A )
  assume climserle.4: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. RR )
  assume climserle.5: |- ( ( ph /\ k e. Z ) -> 0 <_ ( F ` k ) )

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
  assert |- ( ph -> ( seq M ( + , F ) ` N ) <_ A )

  proof
    wph
    cA
    vj
    caddc
    cF
    cM
    cseq
    #
    cM
    cN
    cZ
    clim2ser.1
    climserle.2
    climserle.3
    wph
    cZ
    cr
    vj
    cv
    #
    @0
    wph
    vk
    cF
    cM
    cZ
    clim2ser.1
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    cM
    cz
    wcel
    wph
    cN
    cZ
    @2
    climserle.2
    clim2ser.1
    syl6eleq
    cM
    cN
    eluzel2
    syl
    climserle.4
    serfre
    ffvelrnda
    #
    wph
    @1
    cZ
    wcel
    #
    wa
    #
    @1
    @0
    cfv
    #
    @6
    @1
    c1
    caddc
    co
    #
    cF
    cfv
    #
    caddc
    co
    #
    @7
    @0
    cfv
    #
    cle
    @5
    cc0
    @8
    cle
    wbr
    #
    @6
    @9
    cle
    wbr
    @4
    wph
    @7
    cZ
    wcel
    #
    @11
    cM
    @1
    cZ
    clim2ser.1
    peano2uzs
    #
    @12
    wph
    @11
    wph
    cc0
    vk
    cv
    #
    cF
    cfv
    #
    cle
    wbr
    #
    wi
    wph
    @11
    wi
    vk
    @7
    cZ
    @14
    @7
    wceq
    #
    @16
    @11
    wph
    @17
    @15
    @8
    cc0
    cle
    @14
    @7
    cF
    fveq2
    #
    breq2d
    imbi2d
    wph
    @14
    cZ
    wcel
    #
    @16
    climserle.5
    expcom
    vtoclga
    impcom
    sylan2
    @5
    @6
    @8
    @3
    @4
    wph
    @12
    @8
    cr
    wcel
    #
    @13
    @12
    wph
    @20
    wph
    @15
    cr
    wcel
    #
    wi
    wph
    @20
    wi
    vk
    @7
    cZ
    @17
    @21
    @20
    wph
    @17
    @15
    @8
    cr
    @18
    eleq1d
    imbi2d
    wph
    @19
    @21
    climserle.4
    expcom
    vtoclga
    impcom
    sylan2
    addge01d
    mpbid
    @5
    @1
    @2
    wcel
    @10
    @9
    wceq
    @5
    @1
    cZ
    @2
    wph
    @4
    simpr
    clim2ser.1
    syl6eleq
    caddc
    cF
    cM
    @1
    seqp1
    syl
    breqtrrd
    climub
end
