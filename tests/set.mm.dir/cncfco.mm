include "ccom.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "cncff.mm"
include "syl.mm"
include "fco.mm"
include "syl2anc.mm"
include "wa.mm"
include "adantr.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "simprr.mm"
include "cncfi.mm"
include "syl3anc.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "simpr.mm"
include "ad3antrrr.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "fvco3.mm"
include "oveq12d.mm"
include "imbi2d.mm"
include "sylibrd.mm"
include "imp.mm"
include "an32s.mm"
include "imim2d.mm"
include "anassrs.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "ex.mm"
include "mpid.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "ralrimivva.mm"
include "cc.mm"
include "wss.mm"
include "wb.mm"
include "cncfrss.mm"
include "cncfrss2.mm"
include "elcncf2.mm"
include "mpbir2and.mm"

theorem cncfco
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  assume cncfco.4: |- ( ph -> F e. ( A -cn-> B ) )
  assume cncfco.5: |- ( ph -> G e. ( B -cn-> C ) )


  assert |- ( ph -> ( G o. F ) e. ( A -cn-> C ) )

  proof
    wph
    cG
    cF
    ccom
    #
    cA
    cC
    ccncf
    co
    wcel
    #
    cA
    cC
    @0
    wf
    #
    vw
    cv
    #
    vx
    cv
    #
    cmin
    co
    cabs
    cfv
    vz
    cv
    #
    clt
    wbr
    #
    @3
    @0
    cfv
    #
    @4
    @0
    cfv
    #
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
    cA
    wral
    #
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    vx
    cA
    wral
    #
    wph
    cB
    cC
    cG
    wf
    #
    cA
    cB
    cF
    wf
    #
    @2
    wph
    cG
    cB
    cC
    ccncf
    co
    wcel
    #
    @17
    cncfco.5
    cB
    cC
    cG
    cncff
    syl
    wph
    cF
    cA
    cB
    ccncf
    co
    wcel
    #
    @18
    cncfco.4
    cA
    cB
    cF
    cncff
    syl
    #
    cA
    cB
    cC
    cG
    cF
    fco
    syl2anc
    wph
    @15
    vx
    vy
    cA
    crp
    wph
    @4
    cA
    wcel
    #
    @11
    crp
    wcel
    #
    wa
    #
    wa
    #
    vv
    cv
    #
    @4
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vu
    cv
    #
    clt
    wbr
    #
    @26
    cG
    cfv
    #
    @27
    cG
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @11
    clt
    wbr
    #
    wi
    #
    vv
    cB
    wral
    #
    vu
    crp
    wrex
    #
    @15
    @25
    @19
    @27
    cB
    wcel
    @23
    @39
    wph
    @19
    @24
    cncfco.5
    adantr
    @25
    cA
    cB
    @4
    cF
    wph
    @18
    @24
    @21
    adantr
    wph
    @22
    @23
    simprl
    ffvelrnd
    wph
    @22
    @23
    simprr
    vu
    vv
    cB
    cC
    @27
    @11
    cG
    cncfi
    syl3anc
    @25
    @38
    @15
    vu
    crp
    @25
    @30
    crp
    wcel
    #
    wa
    #
    @38
    @6
    @3
    cF
    cfv
    #
    @27
    cmin
    co
    #
    cabs
    cfv
    #
    @30
    clt
    wbr
    #
    wi
    #
    vw
    cA
    wral
    #
    vz
    crp
    wrex
    #
    @15
    @41
    @20
    @22
    @40
    @48
    wph
    @20
    @24
    @40
    cncfco.4
    ad2antrr
    wph
    @22
    @23
    @40
    simplrl
    #
    @25
    @40
    simpr
    vz
    vw
    cA
    cB
    @4
    @30
    cF
    cncfi
    syl3anc
    @41
    @38
    @48
    @15
    wi
    @41
    @38
    wa
    #
    @47
    @14
    vz
    crp
    @50
    @5
    crp
    wcel
    #
    wa
    @46
    @13
    vw
    cA
    @50
    @51
    @3
    cA
    wcel
    #
    @46
    @13
    wi
    @50
    @51
    @52
    wa
    #
    wa
    @45
    @12
    @6
    @41
    @53
    @38
    @45
    @12
    wi
    #
    @41
    @53
    wa
    #
    @38
    @54
    @55
    @38
    @45
    @42
    cG
    cfv
    #
    @33
    cmin
    co
    #
    cabs
    cfv
    #
    @11
    clt
    wbr
    #
    wi
    #
    @54
    @55
    @42
    cB
    wcel
    @38
    @60
    wi
    @55
    cA
    cB
    @3
    cF
    wph
    @18
    @24
    @40
    @53
    @21
    ad3antrrr
    #
    @41
    @51
    @52
    simprr
    #
    ffvelrnd
    @37
    @60
    vv
    @42
    cB
    @26
    @42
    wceq
    #
    @31
    @45
    @36
    @59
    @63
    @29
    @44
    @30
    clt
    @63
    @28
    @43
    cabs
    @26
    @42
    @27
    cmin
    oveq1
    fveq2d
    breq1d
    @63
    @35
    @58
    @11
    clt
    @63
    @34
    @57
    cabs
    @63
    @32
    @56
    @33
    cmin
    @26
    @42
    cG
    fveq2
    oveq1d
    fveq2d
    breq1d
    imbi12d
    rspcv
    syl
    @55
    @12
    @59
    @45
    @55
    @10
    @58
    @11
    clt
    @55
    @9
    @57
    cabs
    @55
    @7
    @56
    @8
    @33
    cmin
    @55
    @18
    @52
    @7
    @56
    wceq
    @61
    @62
    cA
    cB
    @3
    cG
    cF
    fvco3
    syl2anc
    @55
    @18
    @22
    @8
    @33
    wceq
    @61
    @41
    @22
    @53
    @49
    adantr
    cA
    cB
    @4
    cG
    cF
    fvco3
    syl2anc
    oveq12d
    fveq2d
    breq1d
    imbi2d
    sylibrd
    imp
    an32s
    imim2d
    anassrs
    ralimdva
    reximdva
    ex
    mpid
    rexlimdva
    mpd
    ralrimivva
    wph
    cA
    cc
    wss
    #
    cC
    cc
    wss
    #
    @1
    @2
    @16
    wa
    wb
    wph
    @20
    @64
    cncfco.4
    cA
    cB
    cF
    cncfrss
    syl
    wph
    @19
    @65
    cncfco.5
    cB
    cC
    cG
    cncfrss2
    syl
    vx
    vy
    vz
    vw
    cA
    cC
    @0
    elcncf2
    syl2anc
    mpbir2and
end
