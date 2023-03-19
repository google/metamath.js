include "ccom.mm"
include "cfv.mm"
include "clm.mm"
include "wbr.mm"
include "cuni.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cdm.mm"
include "wa.mm"
include "cuz.mm"
include "wral.mm"
include "cn.mm"
include "wrex.mm"
include "wi.mm"
include "wf.mm"
include "wss.mm"
include "ccnp.mm"
include "eqid.mm"
include "cnpf.mm"
include "syl.mm"
include "w3a.mm"
include "c1.mm"
include "ctop.mm"
include "ctopon.mm"
include "cnptop1.mm"
include "toptopon.mm"
include "sylib.mm"
include "nnuz.mm"
include "1zzd.mm"
include "lmbr2.mm"
include "mpbid.mm"
include "simp1d.mm"
include "cvv.mm"
include "wb.mm"
include "uniexg.mm"
include "cnex.mm"
include "elpm2g.mm"
include "sylancl.mm"
include "simpld.mm"
include "fco.mm"
include "syl2anc.mm"
include "wceq.mm"
include "fdm.mm"
include "feq2d.mm"
include "mpbird.mm"
include "simprd.mm"
include "eqsstrd.mm"
include "cnptop2.mm"
include "mpbir2and.mm"
include "simp2d.mm"
include "ffvelrnd.mm"
include "cima.mm"
include "simp3d.mm"
include "adantr.mm"
include "cnpimaex.mm"
include "3expb.mm"
include "sylan.mm"
include "r19.29.mm"
include "pm3.45.mm"
include "imp.mm"
include "reximi.mm"
include "wfn.mm"
include "ad3antrrr.mm"
include "ffn.mm"
include "simplrl.mm"
include "elssuni.mm"
include "fnfvima.mm"
include "3expia.mm"
include "ad2antrr.mm"
include "fvco3.mm"
include "eleq1d.mm"
include "sylibrd.mm"
include "simplrr.mm"
include "sseld.mm"
include "syld.mm"
include "simpr.mm"
include "eleqtrrd.mm"
include "jctild.mm"
include "expimpd.mm"
include "ralimdv.mm"
include "reximdv.mm"
include "expr.mm"
include "com23.mm"
include "impd.mm"
include "rexlimdva.mm"
include "syl5.mm"
include "mp2and.mm"
include "ralrimiva.mm"
include "mpbir3and.mm"

theorem lmcnp
  let wph: wff ph
  let cP: class P
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let vj: setvar j
  let vk: setvar k
  let vu: setvar u
  let vv: setvar v
  assume lmcnp.3: |- ( ph -> F ( ~~>t ` J ) P )
  assume lmcnp.4: |- ( ph -> G e. ( ( J CnP K ) ` P ) )


  assert |- ( ph -> ( G o. F ) ( ~~>t ` K ) ( G ` P ) )

  proof
    wph
    cG
    cF
    ccom
    #
    cP
    cG
    cfv
    #
    cK
    clm
    cfv
    wbr
    @0
    cK
    cuni
    #
    cc
    cpm
    co
    wcel
    #
    @1
    @2
    wcel
    @1
    vu
    cv
    #
    wcel
    #
    vk
    cv
    #
    @0
    cdm
    #
    wcel
    #
    @6
    @0
    cfv
    #
    @4
    wcel
    #
    wa
    #
    vk
    vj
    cv
    cuz
    cfv
    #
    wral
    #
    vj
    cn
    wrex
    #
    wi
    #
    vu
    cK
    wral
    wph
    @3
    @7
    @2
    @0
    wf
    #
    @7
    cc
    wss
    #
    wph
    @16
    cF
    cdm
    #
    @2
    @0
    wf
    #
    wph
    cJ
    cuni
    #
    @2
    cG
    wf
    #
    @18
    @20
    cF
    wf
    #
    @19
    wph
    cG
    cP
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    @21
    lmcnp.4
    cP
    cG
    cJ
    cK
    @20
    @2
    @20
    eqid
    #
    @2
    eqid
    #
    cnpf
    syl
    #
    wph
    @22
    @18
    cc
    wss
    #
    wph
    cF
    @20
    cc
    cpm
    co
    wcel
    #
    @22
    @27
    wa
    #
    wph
    @28
    cP
    @20
    wcel
    #
    cP
    vv
    cv
    #
    wcel
    #
    @6
    @18
    wcel
    #
    @6
    cF
    cfv
    #
    @31
    wcel
    #
    wa
    #
    vk
    @12
    wral
    #
    vj
    cn
    wrex
    #
    wi
    #
    vv
    cJ
    wral
    #
    wph
    cF
    cP
    cJ
    clm
    cfv
    wbr
    @28
    @30
    @40
    w3a
    lmcnp.3
    wph
    vv
    cP
    vj
    vk
    cF
    cJ
    c1
    @20
    cn
    wph
    cJ
    ctop
    wcel
    #
    cJ
    @20
    ctopon
    cfv
    wcel
    wph
    @23
    @41
    lmcnp.4
    cP
    cG
    cJ
    cK
    cnptop1
    syl
    #
    cJ
    @20
    @24
    toptopon
    sylib
    nnuz
    wph
    1zzd
    #
    lmbr2
    mpbid
    #
    simp1d
    wph
    @20
    cvv
    wcel
    #
    cc
    cvv
    wcel
    #
    @28
    @29
    wb
    wph
    @41
    @45
    @42
    cJ
    ctop
    uniexg
    syl
    cnex
    @20
    cc
    cF
    cvv
    cvv
    elpm2g
    sylancl
    mpbid
    #
    simpld
    #
    @18
    @20
    @2
    cG
    cF
    fco
    syl2anc
    #
    wph
    @7
    @18
    @2
    @0
    wph
    @19
    @7
    @18
    wceq
    #
    @49
    @18
    @2
    @0
    fdm
    syl
    #
    feq2d
    mpbird
    wph
    @7
    @18
    cc
    @51
    wph
    @22
    @27
    @47
    simprd
    eqsstrd
    wph
    @2
    cvv
    wcel
    #
    @46
    @3
    @16
    @17
    wa
    wb
    wph
    cK
    ctop
    wcel
    #
    @52
    wph
    @23
    @53
    lmcnp.4
    cP
    cG
    cJ
    cK
    cnptop2
    syl
    #
    cK
    ctop
    uniexg
    syl
    cnex
    @2
    cc
    @0
    cvv
    cvv
    elpm2g
    sylancl
    mpbir2and
    wph
    @20
    @2
    cP
    cG
    @26
    wph
    @28
    @30
    @40
    @44
    simp2d
    ffvelrnd
    wph
    @15
    vu
    cK
    wph
    @4
    cK
    wcel
    #
    @5
    @14
    wph
    @55
    @5
    wa
    #
    wa
    #
    @40
    @32
    cG
    @31
    cima
    #
    @4
    wss
    #
    wa
    #
    vv
    cJ
    wrex
    #
    @14
    wph
    @40
    @56
    wph
    @28
    @30
    @40
    @44
    simp3d
    adantr
    wph
    @23
    @56
    @61
    lmcnp.4
    @23
    @55
    @5
    @61
    vv
    @4
    cP
    cG
    cJ
    cK
    cnpimaex
    3expb
    sylan
    @40
    @61
    wa
    #
    @38
    @59
    wa
    #
    vv
    cJ
    wrex
    #
    @57
    @14
    @62
    @39
    @60
    wa
    #
    vv
    cJ
    wrex
    @64
    @39
    @60
    vv
    cJ
    r19.29
    @65
    @63
    vv
    cJ
    @39
    @60
    @63
    @32
    @38
    @59
    pm3.45
    imp
    reximi
    syl
    @57
    @63
    @14
    vv
    cJ
    @57
    @31
    cJ
    wcel
    #
    wa
    #
    @38
    @59
    @14
    @67
    @59
    @38
    @14
    @57
    @66
    @59
    @38
    @14
    wi
    @57
    @66
    @59
    wa
    #
    wa
    #
    @37
    @13
    vj
    cn
    @69
    @36
    @11
    vk
    @12
    @69
    @33
    @35
    @11
    @69
    @33
    wa
    #
    @35
    @10
    @8
    @70
    @35
    @9
    @58
    wcel
    #
    @10
    @70
    @35
    @34
    cG
    cfv
    #
    @58
    wcel
    #
    @71
    @70
    cG
    @20
    wfn
    #
    @31
    @20
    wss
    #
    @35
    @73
    wi
    @70
    @21
    @74
    wph
    @21
    @56
    @68
    @33
    @26
    ad3antrrr
    @20
    @2
    cG
    ffn
    syl
    @70
    @66
    @75
    @57
    @66
    @59
    @33
    simplrl
    @31
    cJ
    elssuni
    syl
    @74
    @75
    @35
    @73
    @20
    @31
    cG
    @34
    fnfvima
    3expia
    syl2anc
    @70
    @9
    @72
    @58
    @69
    @22
    @33
    @9
    @72
    wceq
    wph
    @22
    @56
    @68
    @48
    ad2antrr
    @18
    @20
    @6
    cG
    cF
    fvco3
    sylan
    eleq1d
    sylibrd
    @70
    @58
    @4
    @9
    @57
    @66
    @59
    @33
    simplrr
    sseld
    syld
    @70
    @6
    @18
    @7
    @69
    @33
    simpr
    wph
    @50
    @56
    @68
    @33
    @51
    ad3antrrr
    eleqtrrd
    jctild
    expimpd
    ralimdv
    reximdv
    expr
    com23
    impd
    rexlimdva
    syl5
    mp2and
    expr
    ralrimiva
    wph
    vu
    @1
    vj
    vk
    @0
    cK
    c1
    @2
    cn
    wph
    @53
    cK
    @2
    ctopon
    cfv
    wcel
    @54
    cK
    @2
    @25
    toptopon
    sylib
    nnuz
    @43
    lmbr2
    mpbir3and
end
