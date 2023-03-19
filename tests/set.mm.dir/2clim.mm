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
include "c2.mm"
include "cdiv.mm"
include "cc.mm"
include "rphalfcl.mm"
include "wceq.mm"
include "breq2.mm"
include "rexralbidv.mm"
include "rspccva.mm"
include "syl2an.mm"
include "cz.mm"
include "adantr.mm"
include "adantl.mm"
include "eqidd.mm"
include "climi.mm"
include "rexanuz2.mm"
include "sylanbrc.mm"
include "wi.mm"
include "uztrn2.mm"
include "an12.mm"
include "simprr.mm"
include "ad2ant2r.mm"
include "abssubd.mm"
include "breq1d.mm"
include "anbi1d.mm"
include "cr.mm"
include "climcl.mm"
include "syl.mm"
include "ad2antrr.mm"
include "rpre.mm"
include "ad2antlr.mm"
include "abs3lem.mm"
include "syl22anc.mm"
include "sylbid.mm"
include "anassrs.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "sylan2.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "clim2c.mm"
include "mpbird.mm"

theorem 2clim
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vm: setvar m
  let vy: setvar y
  assume 2clim.1: |- Z = ( ZZ>= ` M )
  assume 2clim.2: |- ( ph -> M e. ZZ )
  assume 2clim.3: |- ( ph -> G e. V )
  assume 2clim.5: |- ( ( ph /\ k e. Z ) -> ( G ` k ) e. CC )
  assume 2clim.6: |- ( ph -> A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) ( abs ` ( ( F ` k ) - ( G ` k ) ) ) < x )
  assume 2clim.7: |- ( ph -> F ~~> A )

  disjoint j k
  disjoint A j
  disjoint A k
  disjoint j x
  disjoint F j
  disjoint k x
  disjoint F k
  disjoint F x
  disjoint G j
  disjoint G x
  disjoint M j
  disjoint j ph
  disjoint k ph
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint G k
  disjoint j m
  disjoint j y
  disjoint k m
  disjoint k y
  disjoint m y
  disjoint A m
  disjoint A y
  disjoint m x
  disjoint F m
  disjoint G m
  disjoint x y
  disjoint G y
  disjoint M m
  disjoint V m
  disjoint ph y
  disjoint Z m
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
    cabs
    cfv
    vy
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
    vy
    crp
    wral
    wph
    @7
    vy
    crp
    wph
    @2
    crp
    wcel
    #
    wa
    #
    @0
    cF
    cfv
    #
    @1
    cmin
    co
    cabs
    cfv
    #
    @2
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    @10
    cc
    wcel
    #
    @10
    cA
    cmin
    co
    cabs
    cfv
    @12
    clt
    wbr
    #
    wa
    #
    wa
    #
    vk
    @5
    wral
    #
    vj
    cZ
    wrex
    #
    @7
    @9
    @13
    vk
    @5
    wral
    vj
    cZ
    wrex
    #
    @16
    vk
    @5
    wral
    vj
    cZ
    wrex
    @19
    wph
    @11
    vx
    cv
    #
    clt
    wbr
    #
    vk
    @5
    wral
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    @12
    crp
    wcel
    #
    @20
    @8
    2clim.6
    @2
    rphalfcl
    #
    @23
    @20
    vx
    @12
    crp
    @21
    @12
    wceq
    @22
    @13
    vj
    vk
    cZ
    @5
    @21
    @12
    @11
    clt
    breq2
    rexralbidv
    rspccva
    syl2an
    @9
    cA
    @10
    @12
    vj
    vk
    cF
    cM
    cZ
    2clim.1
    wph
    cM
    cz
    wcel
    @8
    2clim.2
    adantr
    @8
    @24
    wph
    @25
    adantl
    @9
    @0
    cZ
    wcel
    #
    wa
    #
    @10
    eqidd
    wph
    cF
    cA
    cli
    wbr
    #
    @8
    2clim.7
    adantr
    climi
    @13
    @16
    vj
    vk
    cM
    cZ
    2clim.1
    rexanuz2
    sylanbrc
    @9
    @18
    @6
    vj
    cZ
    @9
    @4
    cZ
    wcel
    #
    wa
    @17
    @3
    vk
    @5
    @9
    @29
    @0
    @5
    wcel
    #
    @17
    @3
    wi
    #
    @29
    @30
    wa
    @9
    @26
    @31
    cM
    @0
    @4
    cZ
    2clim.1
    uztrn2
    @17
    @14
    @13
    @15
    wa
    #
    wa
    @27
    @3
    @13
    @14
    @15
    an12
    @27
    @14
    @32
    @3
    @9
    @26
    @14
    @32
    @3
    wi
    @9
    @26
    @14
    wa
    #
    wa
    #
    @32
    @1
    @10
    cmin
    co
    cabs
    cfv
    #
    @12
    clt
    wbr
    #
    @15
    wa
    #
    @3
    @34
    @13
    @36
    @15
    @34
    @11
    @35
    @12
    clt
    @34
    @10
    @1
    @9
    @26
    @14
    simprr
    #
    wph
    @26
    @1
    cc
    wcel
    #
    @8
    @14
    2clim.5
    ad2ant2r
    #
    abssubd
    breq1d
    anbi1d
    @34
    @39
    cA
    cc
    wcel
    #
    @14
    @2
    cr
    wcel
    #
    @37
    @3
    wi
    @40
    wph
    @41
    @8
    @33
    wph
    @28
    @41
    2clim.7
    cA
    cF
    climcl
    syl
    #
    ad2antrr
    @38
    @8
    @42
    wph
    @33
    @2
    rpre
    ad2antlr
    @1
    cA
    @10
    @2
    abs3lem
    syl22anc
    sylbid
    anassrs
    expimpd
    syl5bi
    sylan2
    anassrs
    ralimdva
    reximdva
    mpd
    ralrimiva
    wph
    vy
    cA
    @1
    vj
    vk
    cG
    cM
    cV
    cZ
    2clim.1
    2clim.2
    2clim.3
    wph
    @26
    wa
    @1
    eqidd
    @43
    2clim.5
    clim2c
    mpbird
end
