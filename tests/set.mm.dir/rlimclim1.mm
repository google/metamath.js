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
include "cle.mm"
include "wi.mm"
include "cdm.mm"
include "cr.mm"
include "cvv.mm"
include "fvex.mm"
include "rgenw.mm"
include "a1i.mm"
include "simpr.mm"
include "cmpt.mm"
include "crli.mm"
include "cc.mm"
include "wf.mm"
include "rlimf.mm"
include "syl.mm"
include "adantr.mm"
include "feqmptd.mm"
include "eqbrtrrd.mm"
include "rlimi.mm"
include "cfl.mm"
include "c1.mm"
include "caddc.mm"
include "cif.mm"
include "cz.mm"
include "ad2antrr.mm"
include "flcl.mm"
include "peano2zd.mm"
include "ad2antrl.mm"
include "ifcld.mm"
include "zred.mm"
include "max1.mm"
include "syl2anc.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "syl6eleqr.mm"
include "wss.mm"
include "ad3antrrr.mm"
include "uztrn2.mm"
include "sylan.mm"
include "sseldd.mm"
include "simplrr.mm"
include "simplrl.mm"
include "eluzelre.mm"
include "adantl.mm"
include "fllep1.mm"
include "max2.mm"
include "letrd.mm"
include "eluzle.mm"
include "wceq.mm"
include "breq2.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "ralrimiva.mm"
include "raleqdv.mm"
include "rspcev.mm"
include "rexlimddv.mm"
include "cpm.mm"
include "rlimpm.mm"
include "eqidd.mm"
include "rlimcl.mm"
include "sselda.mm"
include "ffvelrnda.mm"
include "syldan.mm"
include "clim2c.mm"
include "mpbird.mm"

theorem rlimclim1
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume rlimclim1.1: |- Z = ( ZZ>= ` M )
  assume rlimclim1.2: |- ( ph -> M e. ZZ )
  assume rlimclim1.3: |- ( ph -> F ~~>r A )
  assume rlimclim1.4: |- ( ph -> Z C_ dom F )


  assert |- ( ph -> F ~~> A )

  proof
    wph
    cF
    cA
    cli
    wbr
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
    @9
    vy
    crp
    wph
    @4
    crp
    wcel
    #
    wa
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
    @13
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
    wi
    #
    vw
    cF
    cdm
    #
    wral
    #
    @9
    vz
    cr
    @11
    vz
    vw
    @20
    @15
    cA
    @4
    cvv
    @15
    cvv
    wcel
    #
    vw
    @20
    wral
    @11
    @22
    vw
    @20
    @13
    cF
    fvex
    rgenw
    a1i
    wph
    @10
    simpr
    @11
    cF
    vw
    @20
    @15
    cmpt
    cA
    crli
    @11
    vw
    @20
    cc
    cF
    wph
    @20
    cc
    cF
    wf
    #
    @10
    wph
    cF
    cA
    crli
    wbr
    #
    @23
    rlimclim1.3
    cA
    cF
    rlimf
    syl
    #
    adantr
    feqmptd
    wph
    @24
    @10
    rlimclim1.3
    adantr
    eqbrtrrd
    rlimi
    @11
    @12
    cr
    wcel
    #
    @21
    wa
    #
    wa
    #
    cM
    @12
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cle
    wbr
    #
    @30
    cM
    cif
    #
    cZ
    wcel
    #
    @5
    vk
    @32
    cuz
    cfv
    #
    wral
    #
    @9
    @28
    @32
    cM
    cuz
    cfv
    #
    cZ
    @28
    cM
    cz
    wcel
    #
    @32
    cz
    wcel
    cM
    @32
    cle
    wbr
    #
    @32
    @36
    wcel
    wph
    @37
    @10
    @27
    rlimclim1.2
    ad2antrr
    #
    @28
    @31
    @30
    cM
    cz
    @26
    @30
    cz
    wcel
    @11
    @21
    @26
    @29
    @12
    flcl
    peano2zd
    #
    ad2antrl
    #
    @39
    ifcld
    @28
    cM
    cr
    wcel
    #
    @30
    cr
    wcel
    #
    @38
    @28
    cM
    @39
    zred
    #
    @28
    @30
    @41
    zred
    cM
    @30
    max1
    syl2anc
    cM
    @32
    eluz2
    syl3anbrc
    rlimclim1.1
    syl6eleqr
    #
    @28
    @5
    vk
    @34
    @28
    @0
    @34
    wcel
    #
    wa
    #
    @0
    @20
    wcel
    #
    @21
    @12
    @0
    cle
    wbr
    #
    @5
    @47
    cZ
    @20
    @0
    wph
    cZ
    @20
    wss
    @10
    @27
    @46
    rlimclim1.4
    ad3antrrr
    @28
    @33
    @46
    @0
    cZ
    wcel
    #
    @45
    cM
    @0
    @32
    cZ
    rlimclim1.1
    uztrn2
    sylan
    sseldd
    @11
    @26
    @21
    @46
    simplrr
    @47
    @12
    @32
    @0
    @11
    @26
    @21
    @46
    simplrl
    #
    @47
    @31
    @30
    cM
    cr
    @47
    @26
    @43
    @51
    @26
    @30
    @40
    zred
    syl
    #
    @28
    @42
    @46
    @44
    adantr
    #
    ifcld
    #
    @46
    @0
    cr
    wcel
    @28
    @32
    @0
    eluzelre
    adantl
    @47
    @12
    @30
    @32
    @51
    @52
    @54
    @47
    @26
    @12
    @30
    cle
    wbr
    @51
    @12
    fllep1
    syl
    @47
    @42
    @43
    @30
    @32
    cle
    wbr
    @53
    @52
    cM
    @30
    max2
    syl2anc
    letrd
    @46
    @32
    @0
    cle
    wbr
    @28
    @32
    @0
    eluzle
    adantl
    letrd
    @19
    @49
    @5
    wi
    vw
    @0
    @20
    @13
    @0
    wceq
    #
    @14
    @49
    @18
    @5
    @13
    @0
    @12
    cle
    breq2
    @55
    @17
    @3
    @4
    clt
    @55
    @16
    @2
    cabs
    @55
    @15
    @1
    cA
    cmin
    @13
    @0
    cF
    fveq2
    oveq1d
    fveq2d
    breq1d
    imbi12d
    rspcv
    syl3c
    ralrimiva
    @8
    @35
    vj
    @32
    cZ
    @6
    @32
    wceq
    @5
    vk
    @7
    @34
    @6
    @32
    cuz
    fveq2
    raleqdv
    rspcev
    syl2anc
    rexlimddv
    ralrimiva
    wph
    vy
    cA
    @1
    vj
    vk
    cF
    cM
    cc
    cr
    cpm
    co
    #
    cZ
    rlimclim1.1
    rlimclim1.2
    wph
    @24
    cF
    @56
    wcel
    rlimclim1.3
    cA
    cF
    rlimpm
    syl
    wph
    @50
    wa
    @1
    eqidd
    wph
    @24
    cA
    cc
    wcel
    rlimclim1.3
    cA
    cF
    rlimcl
    syl
    wph
    @50
    @48
    @1
    cc
    wcel
    wph
    cZ
    @20
    @0
    rlimclim1.4
    sselda
    wph
    @20
    cc
    @0
    cF
    @25
    ffvelrnda
    syldan
    clim2c
    mpbird
end
