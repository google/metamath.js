include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "cpm.mm"
include "co.mm"
include "wa.mm"
include "cn0.mm"
include "cdvn.mm"
include "cfv.mm"
include "caddc.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "fveq2.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "wss.mm"
include "recnprss.mm"
include "ad2antrr.mm"
include "cdm.mm"
include "cvv.mm"
include "ssid.mm"
include "a1i.mm"
include "wf.mm"
include "wb.mm"
include "cnex.mm"
include "elpm2g.mm"
include "mpan.mm"
include "simplbda.mm"
include "simpl.mm"
include "pmss12g.mm"
include "syl22anc.mm"
include "adantr.mm"
include "dvnff.mm"
include "ffvelrnda.mm"
include "sseldd.mm"
include "dvn0.mm"
include "syl2anc.mm"
include "nn0cn.mm"
include "adantl.mm"
include "addid1d.mm"
include "eqtr4d.mm"
include "cdv.mm"
include "simpr.mm"
include "dvnp1.mm"
include "syl3anc.mm"
include "1cnd.mm"
include "addassd.mm"
include "simpllr.mm"
include "nn0addcl.mm"
include "adantll.mm"
include "eqtr3d.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "com12.mm"
include "impr.mm"

theorem dvnadd
  let cS: class S
  let cF: class F
  let cM: class M
  let cN: class N
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vm: setvar m
  let vs: setvar s


  assert |- ( ( ( S e. { RR , CC } /\ F e. ( CC ^pm S ) ) /\ ( M e. NN0 /\ N e. NN0 ) ) -> ( ( S Dn ( ( S Dn F ) ` M ) ) ` N ) = ( ( S Dn F ) ` ( M + N ) ) )

  proof
    cS
    cr
    cc
    cpr
    #
    wcel
    #
    cF
    cc
    cS
    cpm
    co
    #
    wcel
    #
    wa
    #
    cM
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    cN
    cS
    cM
    cS
    cF
    cdvn
    co
    #
    cfv
    #
    cdvn
    co
    #
    cfv
    #
    cM
    cN
    caddc
    co
    #
    @7
    cfv
    #
    wceq
    #
    @6
    @4
    @5
    wa
    #
    @13
    @14
    vn
    cv
    #
    @9
    cfv
    #
    cM
    @15
    caddc
    co
    #
    @7
    cfv
    #
    wceq
    #
    wi
    @14
    cc0
    @9
    cfv
    #
    cM
    cc0
    caddc
    co
    #
    @7
    cfv
    #
    wceq
    #
    wi
    @14
    vk
    cv
    #
    @9
    cfv
    #
    cM
    @24
    caddc
    co
    #
    @7
    cfv
    #
    wceq
    #
    wi
    @14
    @24
    c1
    caddc
    co
    #
    @9
    cfv
    #
    cM
    @29
    caddc
    co
    #
    @7
    cfv
    #
    wceq
    #
    wi
    @14
    @13
    wi
    vn
    vk
    cN
    @15
    cc0
    wceq
    #
    @19
    @23
    @14
    @34
    @16
    @20
    @18
    @22
    @15
    cc0
    @9
    fveq2
    @34
    @17
    @21
    @7
    @15
    cc0
    cM
    caddc
    oveq2
    fveq2d
    eqeq12d
    imbi2d
    @15
    @24
    wceq
    #
    @19
    @28
    @14
    @35
    @16
    @25
    @18
    @27
    @15
    @24
    @9
    fveq2
    @35
    @17
    @26
    @7
    @15
    @24
    cM
    caddc
    oveq2
    fveq2d
    eqeq12d
    imbi2d
    @15
    @29
    wceq
    #
    @19
    @33
    @14
    @36
    @16
    @30
    @18
    @32
    @15
    @29
    @9
    fveq2
    @36
    @17
    @31
    @7
    @15
    @29
    cM
    caddc
    oveq2
    fveq2d
    eqeq12d
    imbi2d
    @15
    cN
    wceq
    #
    @19
    @13
    @14
    @37
    @16
    @10
    @18
    @12
    @15
    cN
    @9
    fveq2
    @37
    @17
    @11
    @7
    @15
    cN
    cM
    caddc
    oveq2
    fveq2d
    eqeq12d
    imbi2d
    @14
    @20
    @8
    @22
    @14
    cS
    cc
    wss
    #
    @8
    @2
    wcel
    #
    @20
    @8
    wceq
    @1
    @38
    @3
    @5
    cS
    recnprss
    ad2antrr
    #
    @14
    cc
    cF
    cdm
    #
    cpm
    co
    #
    @2
    @8
    @4
    @42
    @2
    wss
    #
    @5
    @4
    cc
    cc
    wss
    #
    @41
    cS
    wss
    #
    cc
    cvv
    wcel
    #
    @1
    @43
    @44
    @4
    cc
    ssid
    a1i
    @1
    @3
    @41
    cc
    cF
    wf
    #
    @45
    @46
    @1
    @3
    @47
    @45
    wa
    wb
    cnex
    cc
    cS
    cF
    cvv
    @0
    elpm2g
    mpan
    simplbda
    @46
    @4
    cnex
    a1i
    @1
    @3
    simpl
    cc
    @41
    cc
    cS
    cvv
    @0
    pmss12g
    syl22anc
    adantr
    @4
    cn0
    @42
    cM
    @7
    cS
    cF
    dvnff
    ffvelrnda
    sseldd
    #
    cS
    @8
    dvn0
    syl2anc
    @14
    @21
    cM
    @7
    @14
    cM
    @5
    cM
    cc
    wcel
    #
    @4
    cM
    nn0cn
    adantl
    #
    addid1d
    fveq2d
    eqtr4d
    @24
    cn0
    wcel
    #
    @14
    @28
    @33
    @14
    @51
    @28
    @33
    wi
    @28
    @33
    @14
    @51
    wa
    #
    cS
    @25
    cdv
    co
    #
    cS
    @27
    cdv
    co
    #
    wceq
    @25
    @27
    cS
    cdv
    oveq2
    @52
    @30
    @53
    @32
    @54
    @52
    @38
    @39
    @51
    @30
    @53
    wceq
    @14
    @38
    @51
    @40
    adantr
    #
    @14
    @39
    @51
    @48
    adantr
    @14
    @51
    simpr
    cS
    @8
    @24
    dvnp1
    syl3anc
    @52
    @26
    c1
    caddc
    co
    #
    @7
    cfv
    #
    @32
    @54
    @52
    @56
    @31
    @7
    @52
    cM
    @24
    c1
    @14
    @49
    @51
    @50
    adantr
    @51
    @24
    cc
    wcel
    @14
    @24
    nn0cn
    adantl
    @52
    1cnd
    addassd
    fveq2d
    @52
    @38
    @3
    @26
    cn0
    wcel
    #
    @57
    @54
    wceq
    @55
    @1
    @3
    @5
    @51
    simpllr
    @5
    @51
    @58
    @4
    cM
    @24
    nn0addcl
    adantll
    cS
    cF
    @26
    dvnp1
    syl3anc
    eqtr3d
    eqeq12d
    syl5ibr
    expcom
    a2d
    nn0ind
    com12
    impr
end
