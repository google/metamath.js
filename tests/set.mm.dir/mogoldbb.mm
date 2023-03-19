include "cv.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cprime.mm"
include "wrex.mm"
include "c6.mm"
include "cuz.mm"
include "cfv.mm"
include "wral.mm"
include "c2.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "ceven.mm"
include "nfra1.mm"
include "wcel.mm"
include "wa.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "2rexbidv.mm"
include "cbvralv.mm"
include "cz.mm"
include "cle.mm"
include "6nn.mm"
include "nnzi.mm"
include "a1i.mm"
include "evenz.mm"
include "2z.mm"
include "zaddcld.mm"
include "adantr.mm"
include "cmin.mm"
include "c4.mm"
include "4cn.mm"
include "2cn.mm"
include "4p2e6.mm"
include "eqcomi.mm"
include "mvrraddi.mm"
include "2p2e4.mm"
include "2evenALTV.mm"
include "evenltle.mm"
include "mp3an2.mm"
include "syl5eqbrr.mm"
include "syl5eqbr.mm"
include "cr.mm"
include "w3a.mm"
include "wb.mm"
include "6re.mm"
include "2re.mm"
include "zred.mm"
include "3jca.mm"
include "lesubadd.mm"
include "syl.mm"
include "mpbid.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "rspcv.mm"
include "syl5bi.mm"
include "nfv.mm"
include "nfre1.mm"
include "nfcv.mm"
include "nfrex.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simpr.mm"
include "simp-4l.mm"
include "mogoldbblem.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "oveq2.mm"
include "cbvrex2v.mm"
include "sylibr.mm"
include "syl3anc.mm"
include "exp31.mm"
include "rexlimdv.mm"
include "expr.mm"
include "rexlimd.mm"
include "ex.mm"
include "syldc.mm"
include "expd.mm"
include "ralrimi.mm"

theorem mogoldbb
  let vn: setvar n
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k

  disjoint n p
  disjoint n q
  disjoint n r
  disjoint p q
  disjoint p r
  disjoint q r
  disjoint m n
  disjoint m p
  disjoint m q
  disjoint m r
  disjoint n x
  disjoint n y
  disjoint p x
  disjoint p y
  disjoint q x
  disjoint q y
  disjoint r x
  disjoint r y
  disjoint x y
  disjoint k x
  assert |- ( A. n e. ( ZZ>= ` 6 ) E. p e. Prime E. q e. Prime E. r e. Prime n = ( ( p + q ) + r ) -> A. n e. Even ( 2 < n -> E. p e. Prime E. q e. Prime n = ( p + q ) ) )

  proof
    vn
    cv
    #
    vp
    cv
    #
    vq
    cv
    #
    caddc
    co
    #
    vr
    cv
    #
    caddc
    co
    #
    wceq
    #
    vr
    cprime
    wrex
    #
    vq
    cprime
    wrex
    vp
    cprime
    wrex
    #
    vn
    c6
    cuz
    cfv
    #
    wral
    #
    c2
    @0
    clt
    wbr
    #
    @0
    @3
    wceq
    #
    vq
    cprime
    wrex
    #
    vp
    cprime
    wrex
    #
    wi
    vn
    ceven
    @8
    vn
    @9
    nfra1
    @10
    @0
    ceven
    wcel
    #
    @11
    @14
    @15
    @11
    wa
    #
    @10
    @0
    c2
    caddc
    co
    #
    @5
    wceq
    #
    vr
    cprime
    wrex
    #
    vq
    cprime
    wrex
    #
    vp
    cprime
    wrex
    #
    @14
    @10
    vm
    cv
    #
    @5
    wceq
    #
    vr
    cprime
    wrex
    #
    vq
    cprime
    wrex
    vp
    cprime
    wrex
    #
    vm
    @9
    wral
    #
    @16
    @21
    @8
    @25
    vn
    vm
    @9
    @0
    @22
    wceq
    #
    @7
    @24
    vp
    vq
    cprime
    cprime
    @27
    @6
    @23
    vr
    cprime
    @0
    @22
    @5
    eqeq1
    rexbidv
    2rexbidv
    cbvralv
    @16
    @17
    @9
    wcel
    #
    @26
    @21
    wi
    @16
    c6
    cz
    wcel
    #
    @17
    cz
    wcel
    #
    c6
    @17
    cle
    wbr
    #
    @28
    @29
    @16
    c6
    6nn
    nnzi
    a1i
    @15
    @30
    @11
    @15
    @0
    c2
    @0
    evenz
    #
    c2
    cz
    wcel
    @15
    2z
    a1i
    zaddcld
    adantr
    @16
    c6
    c2
    cmin
    co
    #
    @0
    cle
    wbr
    #
    @31
    @16
    @33
    c4
    @0
    cle
    c6
    c4
    c2
    4cn
    2cn
    c4
    c2
    caddc
    co
    c6
    4p2e6
    eqcomi
    mvrraddi
    @16
    c4
    c2
    c2
    caddc
    co
    #
    @0
    cle
    2p2e4
    @15
    c2
    ceven
    wcel
    @11
    @35
    @0
    cle
    wbr
    2evenALTV
    c2
    @0
    evenltle
    mp3an2
    syl5eqbrr
    syl5eqbr
    @16
    c6
    cr
    wcel
    #
    c2
    cr
    wcel
    #
    @0
    cr
    wcel
    #
    w3a
    #
    @34
    @31
    wb
    @15
    @39
    @11
    @15
    @36
    @37
    @38
    @36
    @15
    6re
    a1i
    @37
    @15
    2re
    a1i
    @15
    @0
    @32
    zred
    3jca
    adantr
    c6
    c2
    @0
    lesubadd
    syl
    mpbid
    c6
    @17
    eluz2
    syl3anbrc
    @25
    @21
    vm
    @17
    @9
    @22
    @17
    wceq
    #
    @24
    @19
    vp
    vq
    cprime
    cprime
    @40
    @23
    @18
    vr
    cprime
    @22
    @17
    @5
    eqeq1
    rexbidv
    2rexbidv
    rspcv
    syl
    syl5bi
    @16
    @20
    @14
    vp
    cprime
    @16
    vp
    nfv
    @13
    vp
    cprime
    nfre1
    @16
    @1
    cprime
    wcel
    #
    @20
    @14
    wi
    @16
    @41
    wa
    #
    @19
    @14
    vq
    cprime
    @42
    vq
    nfv
    @13
    vq
    vp
    cprime
    vq
    cprime
    nfcv
    @12
    vq
    cprime
    nfre1
    nfrex
    @16
    @41
    @2
    cprime
    wcel
    #
    @19
    @14
    wi
    @16
    @41
    @43
    wa
    #
    wa
    #
    @18
    @14
    vr
    cprime
    @45
    @4
    cprime
    wcel
    #
    @18
    @14
    @45
    @46
    wa
    #
    @18
    wa
    @41
    @43
    @46
    w3a
    #
    @15
    @18
    @14
    @47
    @48
    @18
    @47
    @41
    @43
    @46
    @16
    @41
    @43
    @46
    simplrl
    @16
    @41
    @43
    @46
    simplrr
    @45
    @46
    simpr
    3jca
    adantr
    @15
    @11
    @44
    @46
    @18
    simp-4l
    @47
    @18
    simpr
    @48
    @15
    @18
    w3a
    @0
    vy
    cv
    #
    vx
    cv
    #
    caddc
    co
    #
    wceq
    #
    vx
    cprime
    wrex
    vy
    cprime
    wrex
    @14
    @1
    @2
    @4
    @0
    vx
    vy
    mogoldbblem
    @12
    @52
    @0
    @49
    @2
    caddc
    co
    #
    wceq
    vp
    vq
    vy
    vx
    cprime
    cprime
    @1
    @49
    wceq
    @3
    @53
    @0
    @1
    @49
    @2
    caddc
    oveq1
    eqeq2d
    @2
    @50
    wceq
    @53
    @51
    @0
    @2
    @50
    @49
    caddc
    oveq2
    eqeq2d
    cbvrex2v
    sylibr
    syl3anc
    exp31
    rexlimdv
    expr
    rexlimd
    ex
    rexlimd
    syldc
    expd
    ralrimi
end
