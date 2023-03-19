include "cnrg.mm"
include "wcel.mm"
include "csubrg.mm"
include "cfv.mm"
include "wa.mm"
include "cngp.mm"
include "clmod.mm"
include "csca.mm"
include "w3a.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "cnm.mm"
include "cmul.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "cnlm.mm"
include "nrgngp.mm"
include "adantr.mm"
include "eqidd.mm"
include "csra.mm"
include "a1i.mm"
include "wss.mm"
include "eqid.mm"
include "subrgss.mm"
include "adantl.mm"
include "srabase.mm"
include "cplusg.mm"
include "sraaddg.mm"
include "oveqdr.mm"
include "cds.mm"
include "cxp.mm"
include "srads.mm"
include "reseq1d.mm"
include "sratopn.mm"
include "ngppropd.mm"
include "mpbid.mm"
include "sralmod.mm"
include "cress.mm"
include "srasca.mm"
include "subrgnrg.mm"
include "eqeltrrd.mm"
include "3jca.mm"
include "cmulr.mm"
include "cabv.mm"
include "nrgabv.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "subrgbas.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "eleqtrrd.mm"
include "sseldd.mm"
include "simprr.mm"
include "abvmul.mm"
include "syl3anc.mm"
include "nmpropd.mm"
include "sravsca.mm"
include "fveq12d.mm"
include "eqtr3d.mm"
include "csubg.mm"
include "subrgsubg.mm"
include "ad2antlr.mm"
include "subgnm2.mm"
include "syl2anc.mm"
include "fveq1d.mm"
include "oveq12d.mm"
include "ralrimivva.mm"
include "isnlm.mm"
include "sylanbrc.mm"

theorem sranlm
  let cA: class A
  let cS: class S
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume sranlm.a: |- A = ( ( subringAlg ` W ) ` S )


  assert |- ( ( W e. NrmRing /\ S e. ( SubRing ` W ) ) -> A e. NrmMod )

  proof
    cW
    cnrg
    wcel
    #
    cS
    cW
    csubrg
    cfv
    wcel
    #
    wa
    #
    cA
    cngp
    wcel
    #
    cA
    clmod
    wcel
    #
    cA
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
    cA
    cvsca
    cfv
    #
    co
    #
    cA
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
    cA
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
    cA
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
    @3
    @0
    @20
    @1
    cW
    nrgngp
    adantr
    @2
    vx
    vy
    cW
    cbs
    cfv
    #
    cW
    cA
    @2
    @21
    eqidd
    @2
    cA
    cS
    cW
    cA
    cS
    cW
    csra
    cfv
    cfv
    wceq
    @2
    sranlm.a
    a1i
    #
    @1
    cS
    @21
    wss
    #
    @0
    cS
    @21
    cW
    @21
    eqid
    #
    subrgss
    adantl
    #
    srabase
    #
    @2
    @7
    @21
    wcel
    #
    @8
    @21
    wcel
    #
    wa
    vx
    vy
    cW
    cplusg
    cfv
    cA
    cplusg
    cfv
    @2
    cA
    cS
    cW
    @22
    @25
    sraaddg
    #
    oveqdr
    @2
    cW
    cds
    cfv
    cA
    cds
    cfv
    @21
    @21
    cxp
    @2
    cA
    cS
    cW
    @22
    @25
    srads
    #
    reseq1d
    @2
    cA
    cS
    cW
    @22
    @25
    sratopn
    ngppropd
    mpbid
    @1
    @4
    @0
    cA
    cS
    cW
    sranlm.a
    sralmod
    adantl
    @2
    cW
    cS
    cress
    co
    #
    @5
    cnrg
    @2
    cA
    cS
    cW
    @22
    @25
    srasca
    #
    cS
    cW
    @31
    @31
    eqid
    #
    subrgnrg
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
    cW
    cnm
    cfv
    #
    cfv
    #
    @8
    @38
    cfv
    #
    cmul
    co
    #
    @12
    @16
    @37
    @7
    @8
    cW
    cmulr
    cfv
    #
    co
    #
    @38
    cfv
    #
    @41
    @12
    @37
    @38
    cW
    cabv
    cfv
    #
    wcel
    #
    @27
    @28
    @44
    @41
    wceq
    @0
    @46
    @1
    @36
    @45
    cW
    @38
    @38
    eqid
    #
    @45
    eqid
    #
    nrgabv
    ad2antrr
    @37
    cS
    @21
    @7
    @2
    @23
    @36
    @25
    adantr
    @37
    @7
    @19
    cS
    @2
    @34
    @35
    simprl
    @2
    cS
    @19
    wceq
    @36
    @2
    cS
    @31
    cbs
    cfv
    #
    @19
    @1
    cS
    @49
    wceq
    @0
    cS
    cW
    @31
    @33
    subrgbas
    adantl
    @2
    @31
    @5
    cbs
    @32
    fveq2d
    eqtrd
    adantr
    eleqtrrd
    #
    sseldd
    @37
    @8
    @18
    @21
    @2
    @34
    @35
    simprr
    @2
    @21
    @18
    wceq
    @36
    @26
    adantr
    eleqtrrd
    @45
    @21
    cW
    @42
    @38
    @7
    @8
    @48
    @24
    @42
    eqid
    abvmul
    syl3anc
    @37
    @43
    @10
    @38
    @11
    @2
    @38
    @11
    wceq
    @36
    @2
    cW
    cA
    @26
    @29
    @30
    nmpropd
    adantr
    #
    @2
    @36
    vx
    vy
    @42
    @9
    @2
    cA
    cS
    cW
    @22
    @25
    sravsca
    oveqdr
    fveq12d
    eqtr3d
    @37
    @39
    @14
    @40
    @15
    cmul
    @37
    @7
    @31
    cnm
    cfv
    #
    cfv
    #
    @39
    @14
    @37
    cS
    cW
    csubg
    cfv
    wcel
    #
    @7
    cS
    wcel
    @53
    @39
    wceq
    @1
    @54
    @0
    @36
    cS
    cW
    subrgsubg
    ad2antlr
    @50
    cS
    cW
    @31
    @52
    @38
    @7
    @33
    @47
    @52
    eqid
    subgnm2
    syl2anc
    @37
    @7
    @52
    @13
    @37
    @31
    @5
    cnm
    @2
    @31
    @5
    wceq
    @36
    @32
    adantr
    fveq2d
    fveq1d
    eqtr3d
    @37
    @8
    @38
    @11
    @51
    fveq1d
    oveq12d
    eqtr3d
    ralrimivva
    vx
    vy
    @13
    @9
    @5
    @19
    @11
    @18
    cA
    @18
    eqid
    @11
    eqid
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
