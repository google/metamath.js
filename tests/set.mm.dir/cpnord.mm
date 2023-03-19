include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "cn0.mm"
include "cuz.mm"
include "cfv.mm"
include "ccpn.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "imbi2d.mm"
include "cz.mm"
include "ssid.mm"
include "2a1i.mm"
include "cpm.mm"
include "cdvn.mm"
include "cdm.mm"
include "ccncf.mm"
include "simprl.mm"
include "wf.mm"
include "cdv.mm"
include "recnprss.mm"
include "ad2antrr.mm"
include "adantr.mm"
include "simplll.mm"
include "eluznn0.mm"
include "adantll.mm"
include "dvnf.mm"
include "syl3anc.mm"
include "dvnbss.mm"
include "dvnp1.mm"
include "simprr.mm"
include "eqeltrrd.mm"
include "cncff.mm"
include "syl.mm"
include "fdm.mm"
include "cvv.mm"
include "wb.mm"
include "cnex.mm"
include "elpm2g.mm"
include "sylancr.mm"
include "mpbid.mm"
include "simprd.mm"
include "sstrd.mm"
include "dvbss.mm"
include "eqsstr3d.mm"
include "eqssd.mm"
include "feq2d.mm"
include "dvcn.mm"
include "syl31anc.mm"
include "jca.mm"
include "ex.mm"
include "peano2nn0.mm"
include "elcpn.mm"
include "syl2anc.mm"
include "3imtr4d.mm"
include "ssrdv.mm"
include "sstr2.mm"
include "expcom.mm"
include "a2d.mm"
include "uzind4.mm"
include "com12.mm"
include "3impia.mm"

theorem cpnord
  let cS: class S
  let cM: class M
  let cN: class N
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let cF: class F
  let vm: setvar m
  let vs: setvar s


  assert |- ( ( S e. { RR , CC } /\ M e. NN0 /\ N e. ( ZZ>= ` M ) ) -> ( ( C^n ` S ) ` N ) C_ ( ( C^n ` S ) ` M ) )

  proof
    cS
    cr
    cc
    cpr
    #
    wcel
    #
    cM
    cn0
    wcel
    #
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    cN
    cS
    ccpn
    cfv
    #
    cfv
    #
    cM
    @5
    cfv
    #
    wss
    #
    @4
    @1
    @2
    wa
    #
    @8
    @9
    vn
    cv
    #
    @5
    cfv
    #
    @7
    wss
    #
    wi
    @9
    @7
    @7
    wss
    #
    wi
    @9
    vm
    cv
    #
    @5
    cfv
    #
    @7
    wss
    #
    wi
    @9
    @14
    c1
    caddc
    co
    #
    @5
    cfv
    #
    @7
    wss
    #
    wi
    @9
    @8
    wi
    vn
    vm
    cM
    cN
    @10
    cM
    wceq
    #
    @12
    @13
    @9
    @20
    @11
    @7
    @7
    @10
    cM
    @5
    fveq2
    sseq1d
    imbi2d
    @10
    @14
    wceq
    #
    @12
    @16
    @9
    @21
    @11
    @15
    @7
    @10
    @14
    @5
    fveq2
    sseq1d
    imbi2d
    @10
    @17
    wceq
    #
    @12
    @19
    @9
    @22
    @11
    @18
    @7
    @10
    @17
    @5
    fveq2
    sseq1d
    imbi2d
    @10
    cN
    wceq
    #
    @12
    @8
    @9
    @23
    @11
    @6
    @7
    @10
    cN
    @5
    fveq2
    sseq1d
    imbi2d
    @13
    cM
    cz
    wcel
    @9
    @7
    ssid
    2a1i
    @14
    @3
    wcel
    #
    @9
    @16
    @19
    @9
    @24
    @16
    @19
    wi
    #
    @9
    @24
    wa
    #
    @18
    @15
    wss
    @25
    @26
    vf
    @18
    @15
    @26
    vf
    cv
    #
    cc
    cS
    cpm
    co
    wcel
    #
    @17
    cS
    @27
    cdvn
    co
    #
    cfv
    #
    @27
    cdm
    #
    cc
    ccncf
    co
    #
    wcel
    #
    wa
    #
    @28
    @14
    @29
    cfv
    #
    @32
    wcel
    #
    wa
    #
    @27
    @18
    wcel
    #
    @27
    @15
    wcel
    #
    @26
    @34
    @37
    @26
    @34
    wa
    #
    @28
    @36
    @26
    @28
    @33
    simprl
    #
    @40
    cS
    cc
    wss
    #
    @31
    cc
    @35
    wf
    #
    @31
    cS
    wss
    #
    cS
    @35
    cdv
    co
    #
    cdm
    #
    @31
    wceq
    #
    @36
    @26
    @42
    @34
    @1
    @42
    @2
    @24
    cS
    recnprss
    ad2antrr
    #
    adantr
    #
    @40
    @35
    cdm
    #
    cc
    @35
    wf
    #
    @43
    @40
    @1
    @28
    @14
    cn0
    wcel
    #
    @51
    @1
    @2
    @24
    @34
    simplll
    #
    @41
    @26
    @52
    @34
    @2
    @24
    @52
    @1
    @14
    cM
    eluznn0
    adantll
    #
    adantr
    #
    cS
    @27
    @14
    dvnf
    syl3anc
    #
    @40
    @50
    @31
    cc
    @35
    @40
    @50
    @31
    @40
    @1
    @28
    @52
    @50
    @31
    wss
    @53
    @41
    @55
    cS
    @27
    @14
    dvnbss
    syl3anc
    #
    @40
    @31
    @46
    @50
    @40
    @31
    cc
    @45
    wf
    #
    @47
    @40
    @45
    @32
    wcel
    @58
    @40
    @30
    @45
    @32
    @40
    @42
    @28
    @52
    @30
    @45
    wceq
    @49
    @41
    @55
    cS
    @27
    @14
    dvnp1
    syl3anc
    @26
    @28
    @33
    simprr
    eqeltrrd
    @31
    cc
    @45
    cncff
    syl
    @31
    cc
    @45
    fdm
    syl
    #
    @40
    @50
    cS
    @35
    @49
    @56
    @40
    @50
    @31
    cS
    @57
    @40
    @31
    cc
    @27
    wf
    #
    @44
    @40
    @28
    @60
    @44
    wa
    #
    @41
    @40
    cc
    cvv
    wcel
    @1
    @28
    @61
    wb
    cnex
    @53
    cc
    cS
    @27
    cvv
    @0
    elpm2g
    sylancr
    mpbid
    simprd
    #
    sstrd
    dvbss
    eqsstr3d
    eqssd
    feq2d
    mpbid
    @62
    @59
    @31
    cS
    @35
    dvcn
    syl31anc
    jca
    ex
    @26
    @42
    @17
    cn0
    wcel
    #
    @38
    @34
    wb
    @48
    @26
    @52
    @63
    @54
    @14
    peano2nn0
    syl
    cS
    @27
    @17
    elcpn
    syl2anc
    @26
    @42
    @52
    @39
    @37
    wb
    @48
    @54
    cS
    @27
    @14
    elcpn
    syl2anc
    3imtr4d
    ssrdv
    @18
    @15
    @7
    sstr2
    syl
    expcom
    a2d
    uzind4
    com12
    3impia
end
