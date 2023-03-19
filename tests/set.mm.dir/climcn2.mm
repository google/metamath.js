include "co.mm"
include "cli.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
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
include "simprl.mm"
include "eqidd.mm"
include "climi2.mm"
include "simprr.mm"
include "rexanuz2.mm"
include "sylanbrc.mm"
include "uztrn2.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "anbi1d.mm"
include "oveq1d.mm"
include "imbi12d.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "syl2anc.mm"
include "imp.mm"
include "an32s.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "ex.mm"
include "mpid.mm"
include "rexlimdvva.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "cc.mm"
include "caovcld.mm"
include "jca.mm"
include "ralrimivva.mm"
include "eleq1d.mm"
include "sylc.mm"
include "clim2c.mm"
include "mpbird.mm"

theorem climcn2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cM: class M
  let cW: class W
  let cZ: class Z
  let vj: setvar j
  assume climcn2.1: |- Z = ( ZZ>= ` M )
  assume climcn2.2: |- ( ph -> M e. ZZ )
  assume climcn2.3a: |- ( ph -> A e. C )
  assume climcn2.3b: |- ( ph -> B e. D )
  assume climcn2.4: |- ( ( ph /\ ( u e. C /\ v e. D ) ) -> ( u F v ) e. CC )
  assume climcn2.5a: |- ( ph -> G ~~> A )
  assume climcn2.5b: |- ( ph -> H ~~> B )
  assume climcn2.6: |- ( ph -> K e. W )
  assume climcn2.7: |- ( ( ph /\ x e. RR+ ) -> E. y e. RR+ E. z e. RR+ A. u e. C A. v e. D ( ( ( abs ` ( u - A ) ) < y /\ ( abs ` ( v - B ) ) < z ) -> ( abs ` ( ( u F v ) - ( A F B ) ) ) < x ) )
  assume climcn2.8a: |- ( ( ph /\ k e. Z ) -> ( G ` k ) e. C )
  assume climcn2.8b: |- ( ( ph /\ k e. Z ) -> ( H ` k ) e. D )
  assume climcn2.9: |- ( ( ph /\ k e. Z ) -> ( K ` k ) = ( ( G ` k ) F ( H ` k ) ) )

  disjoint k u
  disjoint k v
  disjoint C k
  disjoint u v
  disjoint C u
  disjoint C v
  disjoint D k
  disjoint D u
  disjoint D v
  disjoint k y
  disjoint k z
  disjoint H k
  disjoint v y
  disjoint v z
  disjoint H v
  disjoint y z
  disjoint H y
  disjoint H z
  disjoint k x
  disjoint k ph
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint ph u
  disjoint v x
  disjoint ph v
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint A k
  disjoint A u
  disjoint A v
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint G k
  disjoint G u
  disjoint G v
  disjoint G y
  disjoint G z
  disjoint K k
  disjoint K x
  disjoint Z k
  disjoint Z y
  disjoint Z z
  disjoint B k
  disjoint B u
  disjoint B v
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint F k
  disjoint F u
  disjoint F v
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint j k
  disjoint j u
  disjoint j v
  disjoint C j
  disjoint D j
  disjoint j y
  disjoint j z
  disjoint H j
  disjoint j x
  disjoint j ph
  disjoint A j
  disjoint G j
  disjoint K j
  disjoint Z j
  disjoint B j
  disjoint F j
  disjoint M j
  assert |- ( ph -> K ~~> ( A F B ) )

  proof
    wph
    cK
    cA
    cB
    cF
    co
    #
    cli
    wbr
    vk
    cv
    #
    cG
    cfv
    #
    @1
    cH
    cfv
    #
    cF
    co
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
    @12
    vx
    crp
    wph
    @7
    crp
    wcel
    #
    wa
    vu
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
    vv
    cv
    #
    cB
    cmin
    co
    #
    cabs
    cfv
    #
    vz
    cv
    #
    clt
    wbr
    #
    wa
    #
    @14
    @19
    cF
    co
    #
    @0
    cmin
    co
    #
    cabs
    cfv
    #
    @7
    clt
    wbr
    #
    wi
    #
    vv
    cD
    wral
    vu
    cC
    wral
    #
    vz
    crp
    wrex
    vy
    crp
    wrex
    #
    @12
    climcn2.7
    wph
    @31
    @12
    wi
    @13
    wph
    @30
    @12
    vy
    vz
    crp
    crp
    wph
    @17
    crp
    wcel
    #
    @22
    crp
    wcel
    #
    wa
    #
    wa
    #
    @30
    @2
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    @17
    clt
    wbr
    #
    @3
    cB
    cmin
    co
    #
    cabs
    cfv
    #
    @22
    clt
    wbr
    #
    wa
    #
    vk
    @10
    wral
    #
    vj
    cZ
    wrex
    #
    @12
    @35
    @38
    vk
    @10
    wral
    vj
    cZ
    wrex
    @41
    vk
    @10
    wral
    vj
    cZ
    wrex
    @44
    @35
    cA
    @2
    @17
    vj
    vk
    cG
    cM
    cZ
    climcn2.1
    wph
    cM
    cz
    wcel
    @34
    climcn2.2
    adantr
    #
    wph
    @32
    @33
    simprl
    @35
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
    @34
    climcn2.5a
    adantr
    climi2
    @35
    cB
    @3
    @22
    vj
    vk
    cH
    cM
    cZ
    climcn2.1
    @45
    wph
    @32
    @33
    simprr
    @47
    @3
    eqidd
    wph
    cH
    cB
    cli
    wbr
    @34
    climcn2.5b
    adantr
    climi2
    @38
    @41
    vj
    vk
    cM
    cZ
    climcn2.1
    rexanuz2
    sylanbrc
    wph
    @30
    @44
    @12
    wi
    #
    wi
    @34
    wph
    @30
    @48
    wph
    @30
    wa
    #
    @43
    @11
    vj
    cZ
    @49
    @9
    cZ
    wcel
    #
    wa
    @42
    @8
    vk
    @10
    @49
    @50
    @1
    @10
    wcel
    #
    @42
    @8
    wi
    #
    @50
    @51
    wa
    @49
    @46
    @52
    cM
    @1
    @9
    cZ
    climcn2.1
    uztrn2
    wph
    @46
    @30
    @52
    wph
    @46
    wa
    #
    @30
    @52
    @53
    @2
    cC
    wcel
    #
    @3
    cD
    wcel
    #
    @30
    @52
    wi
    climcn2.8a
    climcn2.8b
    @29
    @52
    @38
    @23
    wa
    #
    @2
    @19
    cF
    co
    #
    @0
    cmin
    co
    #
    cabs
    cfv
    #
    @7
    clt
    wbr
    #
    wi
    vu
    vv
    @2
    @3
    cC
    cD
    @14
    @2
    wceq
    #
    @24
    @56
    @28
    @60
    @61
    @18
    @38
    @23
    @61
    @16
    @37
    @17
    clt
    @61
    @15
    @36
    cabs
    @14
    @2
    cA
    cmin
    oveq1
    fveq2d
    breq1d
    anbi1d
    @61
    @27
    @59
    @7
    clt
    @61
    @26
    @58
    cabs
    @61
    @25
    @57
    @0
    cmin
    @14
    @2
    @19
    cF
    oveq1
    #
    oveq1d
    fveq2d
    breq1d
    imbi12d
    @19
    @3
    wceq
    #
    @56
    @42
    @60
    @8
    @63
    @23
    @41
    @38
    @63
    @21
    @40
    @22
    clt
    @63
    @20
    @39
    cabs
    @19
    @3
    cB
    cmin
    oveq1
    fveq2d
    breq1d
    anbi2d
    @63
    @59
    @6
    @7
    clt
    @63
    @58
    @5
    cabs
    @63
    @57
    @4
    @0
    cmin
    @19
    @3
    @2
    cF
    oveq2
    #
    oveq1d
    fveq2d
    breq1d
    imbi12d
    rspc2v
    syl2anc
    imp
    an32s
    sylan2
    anassrs
    ralimdva
    reximdva
    ex
    adantr
    mpid
    rexlimdvva
    adantr
    mpd
    ralrimiva
    wph
    vx
    @0
    @4
    vj
    vk
    cK
    cM
    cW
    cZ
    climcn2.1
    climcn2.2
    climcn2.6
    climcn2.9
    wph
    vu
    vv
    cA
    cB
    cC
    cD
    cc
    cF
    climcn2.4
    climcn2.3a
    climcn2.3b
    caovcld
    @53
    @54
    @55
    wa
    @25
    cc
    wcel
    #
    vv
    cD
    wral
    vu
    cC
    wral
    #
    @4
    cc
    wcel
    #
    @53
    @54
    @55
    climcn2.8a
    climcn2.8b
    jca
    wph
    @66
    @46
    wph
    @65
    vu
    vv
    cC
    cD
    climcn2.4
    ralrimivva
    adantr
    @65
    @67
    @57
    cc
    wcel
    vu
    vv
    @2
    @3
    cC
    cD
    @61
    @25
    @57
    cc
    @62
    eleq1d
    @63
    @57
    @4
    cc
    @64
    eleq1d
    rspc2v
    sylc
    clim2c
    mpbird
end
