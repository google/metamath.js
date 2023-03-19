include "cnlm.mm"
include "wcel.mm"
include "wa.mm"
include "cngp.mm"
include "clmod.mm"
include "csca.mm"
include "cfv.mm"
include "cnrg.mm"
include "w3a.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "cnm.mm"
include "cmul.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "csubg.mm"
include "nlmngp.mm"
include "adantr.mm"
include "nlmlmod.mm"
include "lsssubg.mm"
include "sylan.mm"
include "subgngp.mm"
include "syl2anc.mm"
include "lsslmod.mm"
include "eqid.mm"
include "resssca.mm"
include "adantl.mm"
include "nlmnrg.mm"
include "eqeltrrd.mm"
include "3jca.mm"
include "simpll.mm"
include "simprl.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "wss.mm"
include "subgss.mm"
include "syl.mm"
include "simprr.mm"
include "subgbas.mm"
include "sseldd.mm"
include "nmvs.mm"
include "syl3anc.mm"
include "simplr.mm"
include "ressvsca.mm"
include "oveqd.mm"
include "ad2antrr.mm"
include "lssvscl.mm"
include "syl22anc.mm"
include "subgnm2.mm"
include "eqtr3d.mm"
include "eqcomd.mm"
include "fveq1d.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "isnlm.mm"
include "sylanbrc.mm"

theorem lssnlm
  let cS: class S
  let cU: class U
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume lssnlm.x: |- X = ( W |`s U )
  assume lssnlm.s: |- S = ( LSubSp ` W )


  assert |- ( ( W e. NrmMod /\ U e. S ) -> X e. NrmMod )

  proof
    cW
    cnlm
    wcel
    #
    cU
    cS
    wcel
    #
    wa
    #
    cX
    cngp
    wcel
    #
    cX
    clmod
    wcel
    #
    cX
    csca
    cfv
    #
    cnrg
    wcel
    #
    w3a
    vx
    cv
    #
    vy
    cv
    #
    cX
    cvsca
    cfv
    #
    co
    #
    cX
    cnm
    cfv
    #
    cfv
    #
    @7
    @5
    cnm
    cfv
    #
    cfv
    #
    @8
    @11
    cfv
    #
    cmul
    co
    #
    wceq
    #
    vy
    cX
    cbs
    cfv
    #
    wral
    vx
    @5
    cbs
    cfv
    #
    wral
    cX
    cnlm
    wcel
    @2
    @3
    @4
    @6
    @2
    cW
    cngp
    wcel
    #
    cU
    cW
    csubg
    cfv
    wcel
    #
    @3
    @0
    @20
    @1
    cW
    nlmngp
    adantr
    @0
    cW
    clmod
    wcel
    #
    @1
    @21
    cW
    nlmlmod
    #
    cS
    cU
    cW
    lssnlm.s
    lsssubg
    sylan
    #
    cU
    cW
    cX
    lssnlm.x
    subgngp
    syl2anc
    @0
    @22
    @1
    @4
    @23
    cS
    cU
    cW
    cX
    lssnlm.x
    lssnlm.s
    lsslmod
    sylan
    @2
    cW
    csca
    cfv
    #
    @5
    cnrg
    @1
    @25
    @5
    wceq
    #
    @0
    cU
    @25
    cW
    cX
    cS
    lssnlm.x
    @25
    eqid
    #
    resssca
    adantl
    #
    @0
    @25
    cnrg
    wcel
    @1
    @25
    cW
    @27
    nlmnrg
    adantr
    eqeltrrd
    3jca
    @2
    @17
    vx
    vy
    @19
    @18
    @2
    @7
    @19
    wcel
    #
    @8
    @18
    wcel
    #
    wa
    #
    wa
    #
    @7
    @8
    cW
    cvsca
    cfv
    #
    co
    #
    cW
    cnm
    cfv
    #
    cfv
    #
    @7
    @25
    cnm
    cfv
    #
    cfv
    #
    @8
    @35
    cfv
    #
    cmul
    co
    #
    @12
    @16
    @32
    @0
    @7
    @25
    cbs
    cfv
    #
    wcel
    #
    @8
    cW
    cbs
    cfv
    #
    wcel
    @36
    @40
    wceq
    @0
    @1
    @31
    simpll
    @32
    @7
    @19
    @41
    @2
    @29
    @30
    simprl
    @32
    @25
    @5
    cbs
    @2
    @26
    @31
    @28
    adantr
    #
    fveq2d
    eleqtrrd
    #
    @32
    cU
    @43
    @8
    @32
    @21
    cU
    @43
    wss
    @2
    @21
    @31
    @24
    adantr
    #
    @43
    cU
    cW
    @43
    eqid
    #
    subgss
    syl
    @32
    @8
    @18
    cU
    @2
    @29
    @30
    simprr
    @32
    @21
    cU
    @18
    wceq
    @46
    cU
    cW
    cX
    lssnlm.x
    subgbas
    syl
    eleqtrrd
    #
    sseldd
    @37
    @33
    @25
    @41
    @35
    @43
    cW
    @7
    @8
    @47
    @35
    eqid
    #
    @33
    eqid
    #
    @27
    @41
    eqid
    #
    @37
    eqid
    nmvs
    syl3anc
    @32
    @34
    @11
    cfv
    #
    @12
    @36
    @32
    @34
    @10
    @11
    @32
    @33
    @9
    @7
    @8
    @32
    @1
    @33
    @9
    wceq
    @0
    @1
    @31
    simplr
    #
    cU
    @33
    cW
    cX
    cS
    lssnlm.x
    @50
    ressvsca
    syl
    oveqd
    fveq2d
    @32
    @21
    @34
    cU
    wcel
    #
    @52
    @36
    wceq
    @46
    @32
    @22
    @1
    @42
    @8
    cU
    wcel
    #
    @54
    @0
    @22
    @1
    @31
    @23
    ad2antrr
    @53
    @45
    @48
    @41
    cS
    @33
    cU
    @25
    cW
    @7
    @8
    @27
    @50
    @51
    lssnlm.s
    lssvscl
    syl22anc
    cU
    cW
    cX
    @11
    @35
    @34
    lssnlm.x
    @49
    @11
    eqid
    #
    subgnm2
    syl2anc
    eqtr3d
    @32
    @14
    @38
    @15
    @39
    cmul
    @32
    @7
    @13
    @37
    @32
    @5
    @25
    cnm
    @32
    @25
    @5
    @44
    eqcomd
    fveq2d
    fveq1d
    @32
    @21
    @55
    @15
    @39
    wceq
    @46
    @48
    cU
    cW
    cX
    @11
    @35
    @8
    lssnlm.x
    @49
    @56
    subgnm2
    syl2anc
    oveq12d
    3eqtr4d
    ralrimivva
    vx
    vy
    @13
    @9
    @5
    @19
    @11
    @18
    cX
    @18
    eqid
    @56
    @9
    eqid
    @5
    eqid
    @19
    eqid
    @13
    eqid
    isnlm
    sylanbrc
end
