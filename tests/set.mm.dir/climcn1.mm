include "cfv.mm"
include "cli.mm"
include "wbr.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "cz.mm"
include "adantr.mm"
include "simpr.mm"
include "eqidd.mm"
include "climi2.mm"
include "uztrn2.mm"
include "adantlr.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "sylan.mm"
include "an32s.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "ex.mm"
include "mpid.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "cc.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "clim2c.mm"
include "mpbird.mm"

theorem climcn1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cW: class W
  let cZ: class Z
  let vj: setvar j
  assume climcn1.1: |- Z = ( ZZ>= ` M )
  assume climcn1.2: |- ( ph -> M e. ZZ )
  assume climcn1.3: |- ( ph -> A e. B )
  assume climcn1.4: |- ( ( ph /\ z e. B ) -> ( F ` z ) e. CC )
  assume climcn1.5: |- ( ph -> G ~~> A )
  assume climcn1.6: |- ( ph -> H e. W )
  assume climcn1.7: |- ( ( ph /\ x e. RR+ ) -> E. y e. RR+ A. z e. B ( ( abs ` ( z - A ) ) < y -> ( abs ` ( ( F ` z ) - ( F ` A ) ) ) < x ) )
  assume climcn1.8: |- ( ( ph /\ k e. Z ) -> ( G ` k ) e. B )
  assume climcn1.9: |- ( ( ph /\ k e. Z ) -> ( H ` k ) = ( F ` ( G ` k ) ) )

  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B k
  disjoint B z
  disjoint G k
  disjoint G y
  disjoint G z
  disjoint H k
  disjoint H x
  disjoint F k
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint Z k
  disjoint Z y
  disjoint j k
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint A j
  disjoint B j
  disjoint G j
  disjoint H j
  disjoint M j
  disjoint F j
  disjoint j ph
  disjoint Z j
  assert |- ( ph -> H ~~> ( F ` A ) )

  proof
    wph
    cH
    cA
    cF
    cfv
    #
    cli
    wbr
    vk
    cv
    #
    cG
    cfv
    #
    cF
    cfv
    #
    @0
    cmin
    co
    #
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    wph
    @11
    vx
    crp
    wph
    @6
    crp
    wcel
    #
    wa
    vz
    cv
    #
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    @13
    cF
    cfv
    #
    @0
    cmin
    co
    #
    cabs
    cfv
    #
    @6
    clt
    wbr
    #
    wi
    #
    vz
    cB
    wral
    #
    vy
    crp
    wrex
    #
    @11
    climcn1.7
    wph
    @24
    @11
    wi
    @12
    wph
    @23
    @11
    vy
    crp
    wph
    @16
    crp
    wcel
    #
    wa
    #
    @23
    @2
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    @16
    clt
    wbr
    #
    vk
    @9
    wral
    #
    vj
    cZ
    wrex
    #
    @11
    @26
    cA
    @2
    @16
    vj
    vk
    cG
    cM
    cZ
    climcn1.1
    wph
    cM
    cz
    wcel
    @25
    climcn1.2
    adantr
    wph
    @25
    simpr
    @26
    @1
    cZ
    wcel
    #
    wa
    #
    @2
    eqidd
    wph
    cG
    cA
    cli
    wbr
    @25
    climcn1.5
    adantr
    climi2
    @26
    @23
    @31
    @11
    wi
    @26
    @23
    wa
    #
    @30
    @10
    vj
    cZ
    @34
    @8
    cZ
    wcel
    #
    wa
    @29
    @7
    vk
    @9
    @34
    @35
    @1
    @9
    wcel
    #
    @29
    @7
    wi
    #
    @35
    @36
    wa
    @34
    @32
    @37
    cM
    @1
    @8
    cZ
    climcn1.1
    uztrn2
    @26
    @32
    @23
    @37
    @33
    @2
    cB
    wcel
    #
    @23
    @37
    wph
    @32
    @38
    @25
    climcn1.8
    adantlr
    @22
    @37
    vz
    @2
    cB
    @13
    @2
    wceq
    #
    @17
    @29
    @21
    @7
    @39
    @15
    @28
    @16
    clt
    @39
    @14
    @27
    cabs
    @13
    @2
    cA
    cmin
    oveq1
    fveq2d
    breq1d
    @39
    @20
    @5
    @6
    clt
    @39
    @19
    @4
    cabs
    @39
    @18
    @3
    @0
    cmin
    @13
    @2
    cF
    fveq2
    #
    oveq1d
    fveq2d
    breq1d
    imbi12d
    rspcva
    sylan
    an32s
    sylan2
    anassrs
    ralimdva
    reximdva
    ex
    mpid
    rexlimdva
    adantr
    mpd
    ralrimiva
    wph
    vx
    @0
    @3
    vj
    vk
    cH
    cM
    cW
    cZ
    climcn1.1
    climcn1.2
    climcn1.6
    climcn1.9
    wph
    cA
    cB
    wcel
    @18
    cc
    wcel
    #
    vz
    cB
    wral
    #
    @0
    cc
    wcel
    #
    climcn1.3
    wph
    @41
    vz
    cB
    climcn1.4
    ralrimiva
    #
    @41
    @43
    vz
    cA
    cB
    @13
    cA
    wceq
    @18
    @0
    cc
    @13
    cA
    cF
    fveq2
    eleq1d
    rspcv
    sylc
    wph
    @32
    wa
    @38
    @42
    @3
    cc
    wcel
    #
    climcn1.8
    wph
    @42
    @32
    @44
    adantr
    @41
    @45
    vz
    @2
    cB
    @39
    @18
    @3
    cc
    @40
    eleq1d
    rspcv
    sylc
    clim2c
    mpbird
end
