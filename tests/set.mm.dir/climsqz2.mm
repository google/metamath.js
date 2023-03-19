include "cli.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
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
include "cz.mm"
include "adantr.mm"
include "simpr.mm"
include "eqidd.mm"
include "climi2.mm"
include "wi.mm"
include "uztrn2.mm"
include "cle.mm"
include "cr.mm"
include "climrecl.mm"
include "lesub1dd.mm"
include "abssubge0d.mm"
include "letrd.mm"
include "3brtr4d.mm"
include "adantlr.mm"
include "ad2antrr.mm"
include "resubcld.mm"
include "recnd.mm"
include "abscld.mm"
include "rpre.mm"
include "ad2antlr.mm"
include "lelttr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "clim2c.mm"
include "mpbird.mm"

theorem climsqz2
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cW: class W
  let cZ: class Z
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let vj: setvar j
  let cH: class H
  assume climadd.1: |- Z = ( ZZ>= ` M )
  assume climadd.2: |- ( ph -> M e. ZZ )
  assume climadd.4: |- ( ph -> F ~~> A )
  assume climsqz.5: |- ( ph -> G e. W )
  assume climsqz.6: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. RR )
  assume climsqz.7: |- ( ( ph /\ k e. Z ) -> ( G ` k ) e. RR )
  assume climsqz2.8: |- ( ( ph /\ k e. Z ) -> ( G ` k ) <_ ( F ` k ) )
  assume climsqz2.9: |- ( ( ph /\ k e. Z ) -> A <_ ( G ` k ) )

  disjoint F k
  disjoint k ph
  disjoint A k
  disjoint G k
  disjoint M k
  disjoint Z k
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint B k
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C k
  disjoint j k
  disjoint j u
  disjoint j v
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint F u
  disjoint F v
  disjoint F y
  disjoint F z
  disjoint j x
  disjoint j ph
  disjoint ph u
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint A j
  disjoint A u
  disjoint A v
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint G j
  disjoint G v
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint H k
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint M j
  disjoint M x
  disjoint Z j
  disjoint Z x
  disjoint Z y
  disjoint Z z
  assert |- ( ph -> G ~~> A )

  proof
    wph
    cG
    cA
    cli
    wbr
    vk
    cv
    #
    cG
    cfv
    #
    cA
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
    @9
    vx
    crp
    wph
    @4
    crp
    wcel
    #
    wa
    #
    @0
    cF
    cfv
    #
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    @4
    clt
    wbr
    #
    vk
    @7
    wral
    #
    vj
    cZ
    wrex
    @9
    @11
    cA
    @12
    @4
    vj
    vk
    cF
    cM
    cZ
    climadd.1
    wph
    cM
    cz
    wcel
    @10
    climadd.2
    adantr
    wph
    @10
    simpr
    @11
    @0
    cZ
    wcel
    #
    wa
    #
    @12
    eqidd
    wph
    cF
    cA
    cli
    wbr
    @10
    climadd.4
    adantr
    climi2
    @11
    @16
    @8
    vj
    cZ
    @11
    @6
    cZ
    wcel
    #
    wa
    @15
    @5
    vk
    @7
    @11
    @19
    @0
    @7
    wcel
    #
    @15
    @5
    wi
    #
    @19
    @20
    wa
    @11
    @17
    @21
    cM
    @0
    @6
    cZ
    climadd.1
    uztrn2
    @18
    @3
    @14
    cle
    wbr
    #
    @15
    @5
    wph
    @17
    @22
    @10
    wph
    @17
    wa
    #
    @2
    @13
    @3
    @14
    cle
    @23
    @1
    @12
    cA
    climsqz.7
    climsqz.6
    wph
    cA
    cr
    wcel
    #
    @17
    wph
    cA
    vk
    cF
    cM
    cZ
    climadd.1
    climadd.2
    climadd.4
    climsqz.6
    climrecl
    #
    adantr
    #
    climsqz2.8
    lesub1dd
    @23
    cA
    @1
    @26
    climsqz.7
    climsqz2.9
    abssubge0d
    @23
    cA
    @12
    @26
    climsqz.6
    @23
    cA
    @1
    @12
    @26
    climsqz.7
    climsqz.6
    climsqz2.9
    climsqz2.8
    letrd
    abssubge0d
    3brtr4d
    adantlr
    @18
    @3
    cr
    wcel
    @14
    cr
    wcel
    @4
    cr
    wcel
    #
    @22
    @15
    wa
    @5
    wi
    @18
    @2
    @18
    @2
    @18
    @1
    cA
    wph
    @17
    @1
    cr
    wcel
    @10
    climsqz.7
    adantlr
    wph
    @24
    @10
    @17
    @25
    ad2antrr
    #
    resubcld
    recnd
    abscld
    @18
    @13
    @18
    @13
    @18
    @12
    cA
    wph
    @17
    @12
    cr
    wcel
    @10
    climsqz.6
    adantlr
    @28
    resubcld
    recnd
    abscld
    @10
    @27
    wph
    @17
    @4
    rpre
    ad2antlr
    @3
    @14
    @4
    lelttr
    syl3anc
    mpand
    sylan2
    anassrs
    ralimdva
    reximdva
    mpd
    ralrimiva
    wph
    vx
    cA
    @1
    vj
    vk
    cG
    cM
    cW
    cZ
    climadd.1
    climadd.2
    climsqz.5
    @23
    @1
    eqidd
    wph
    cA
    @25
    recnd
    @23
    @1
    climsqz.7
    recnd
    clim2c
    mpbird
end
