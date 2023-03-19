include "crli.mm"
include "wbr.mm"
include "cli.mm"
include "wa.mm"
include "cz.mm"
include "wcel.mm"
include "adantr.mm"
include "simpr.mm"
include "cdm.mm"
include "wss.mm"
include "cc.mm"
include "wf.mm"
include "wceq.mm"
include "fdm.mm"
include "eqimss2.mm"
include "3syl.mm"
include "rlimclim1.mm"
include "cv.mm"
include "cle.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "crp.mm"
include "climcl.mm"
include "adantl.mm"
include "cuz.mm"
include "ad2antrr.mm"
include "eqidd.mm"
include "simplr.mm"
include "climi2.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "simplrl.mm"
include "sseldi.mm"
include "simprl.mm"
include "simprr.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "simplrr.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "expr.mm"
include "ralrimiva.mm"
include "reximdva.mm"
include "zssre.mm"
include "sstri.mm"
include "ssrexv.mm"
include "ax-mp.mm"
include "syl6.mm"
include "mpd.mm"
include "a1i.mm"
include "rlim.mm"
include "mpbir2and.mm"
include "impbida.mm"

theorem rlimclim
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume rlimclim.1: |- Z = ( ZZ>= ` M )
  assume rlimclim.2: |- ( ph -> M e. ZZ )
  assume rlimclim.3: |- ( ph -> F : Z --> CC )


  assert |- ( ph -> ( F ~~>r A <-> F ~~> A ) )

  proof
    wph
    cF
    cA
    crli
    wbr
    #
    cF
    cA
    cli
    wbr
    #
    wph
    @0
    wa
    cA
    cF
    cM
    cZ
    rlimclim.1
    wph
    cM
    cz
    wcel
    #
    @0
    rlimclim.2
    adantr
    wph
    @0
    simpr
    wph
    cZ
    cF
    cdm
    #
    wss
    #
    @0
    wph
    cZ
    cc
    cF
    wf
    #
    @3
    cZ
    wceq
    @4
    rlimclim.3
    cZ
    cc
    cF
    fdm
    cZ
    @3
    eqimss2
    3syl
    adantr
    rlimclim1
    wph
    @1
    wa
    #
    @0
    cA
    cc
    wcel
    #
    vz
    cv
    #
    vw
    cv
    #
    cle
    wbr
    #
    @9
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
    vy
    cv
    #
    clt
    wbr
    #
    wi
    #
    vw
    cZ
    wral
    #
    vz
    cr
    wrex
    #
    vy
    crp
    wral
    @1
    @7
    wph
    cA
    cF
    climcl
    adantl
    @6
    @18
    vy
    crp
    @6
    @14
    crp
    wcel
    #
    wa
    #
    vk
    cv
    #
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
    @14
    clt
    wbr
    #
    vk
    @8
    cuz
    cfv
    #
    wral
    #
    vz
    cZ
    wrex
    #
    @18
    @20
    cA
    @22
    @14
    vz
    vk
    cF
    cM
    cZ
    rlimclim.1
    wph
    @2
    @1
    @19
    rlimclim.2
    ad2antrr
    @6
    @19
    simpr
    @20
    @21
    cZ
    wcel
    wa
    @22
    eqidd
    wph
    @1
    @19
    simplr
    climi2
    @20
    @28
    @17
    vz
    cZ
    wrex
    #
    @18
    @20
    @27
    @17
    vz
    cZ
    @20
    @8
    cZ
    wcel
    #
    @27
    @17
    @20
    @30
    @27
    wa
    wa
    #
    @16
    vw
    cZ
    @31
    @9
    cZ
    wcel
    #
    @10
    @15
    @31
    @32
    @10
    wa
    #
    wa
    #
    @9
    @26
    wcel
    #
    @27
    @15
    @34
    @8
    cz
    wcel
    @9
    cz
    wcel
    @10
    @35
    @34
    cZ
    cz
    @8
    cZ
    cM
    cuz
    cfv
    cz
    rlimclim.1
    cM
    uzssz
    eqsstri
    #
    @20
    @30
    @27
    @33
    simplrl
    sseldi
    @34
    cZ
    cz
    @9
    @36
    @31
    @32
    @10
    simprl
    sseldi
    @31
    @32
    @10
    simprr
    @8
    @9
    eluz2
    syl3anbrc
    @20
    @30
    @27
    @33
    simplrr
    @25
    @15
    vk
    @9
    @26
    @21
    @9
    wceq
    #
    @24
    @13
    @14
    clt
    @37
    @23
    @12
    cabs
    @37
    @22
    @11
    cA
    cmin
    @21
    @9
    cF
    fveq2
    oveq1d
    fveq2d
    breq1d
    rspcv
    sylc
    expr
    ralrimiva
    expr
    reximdva
    cZ
    cr
    wss
    #
    @29
    @18
    wi
    cZ
    cz
    cr
    @36
    zssre
    sstri
    #
    @17
    vz
    cZ
    cr
    ssrexv
    ax-mp
    syl6
    mpd
    ralrimiva
    @6
    vy
    vz
    vw
    cZ
    @11
    cA
    cF
    wph
    @5
    @1
    rlimclim.3
    adantr
    @38
    @6
    @39
    a1i
    @6
    @32
    wa
    @11
    eqidd
    rlim
    mpbir2and
    impbida
end
