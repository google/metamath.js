include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cprime.mm"
include "wrex.mm"
include "wnel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfzo.mm"
include "wral.mm"
include "wa.mm"
include "prmunb.mm"
include "w3a.mm"
include "cle.mm"
include "crab.mm"
include "eqid.mm"
include "prmgaplem4.mm"
include "wi.mm"
include "wceq.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "elrab.mm"
include "simplrl.mm"
include "simprrl.mm"
include "adantr.mm"
include "simpll.mm"
include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "elfzo2.mm"
include "eluz2.mm"
include "wb.mm"
include "nnz.mm"
include "prmz.mm"
include "zltp1le.mm"
include "syl2an.mm"
include "exbiri.mm"
include "3ad2ant1.mm"
include "impcom.mm"
include "com12.mm"
include "imp.mm"
include "cr.mm"
include "prmnn.mm"
include "nnred.mm"
include "ad2antrl.mm"
include "adantl.mm"
include "ltleletr.mm"
include "syl3anc.mm"
include "exp4b.mm"
include "3ad2ant2.mm"
include "expdcom.mm"
include "com45.mm"
include "com14.mm"
include "adantld.mm"
include "jca.mm"
include "exp41.mm"
include "3ad2ant3.mm"
include "sylbi.mm"
include "3imp.mm"
include "sylanbrc.mm"
include "elfzolt2.mm"
include "wn.mm"
include "ltnle.mm"
include "biimpd.mm"
include "pm2.21d.mm"
include "sylan2.mm"
include "embantd.mm"
include "ex.mm"
include "com23.mm"
include "df-nel.mm"
include "ax-1.mm"
include "a1d.mm"
include "sylbir.mm"
include "pm2.61i.mm"
include "ralimdv2.mm"
include "jca32.mm"
include "syl5bi.mm"
include "impd.mm"
include "reximdv2.mm"
include "mpd.mm"
include "rexlimdv3a.mm"

theorem prmgaplem6
  let vz: setvar z
  let cN: class N
  let vp: setvar p
  let vn: setvar n
  let vq: setvar q
  let vr: setvar r

  disjoint N p
  disjoint N z
  disjoint p z
  disjoint N n
  disjoint N q
  disjoint N r
  disjoint n p
  disjoint n q
  disjoint n r
  disjoint n z
  disjoint p q
  disjoint p r
  disjoint q r
  disjoint q z
  disjoint r z
  assert |- ( N e. NN -> E. p e. Prime ( N < p /\ A. z e. ( ( N + 1 ) ..^ p ) z e/ Prime ) )

  proof
    cN
    cn
    wcel
    #
    cN
    vn
    cv
    #
    clt
    wbr
    #
    vn
    cprime
    wrex
    cN
    vp
    cv
    #
    clt
    wbr
    #
    vz
    cv
    #
    cprime
    wnel
    #
    vz
    cN
    c1
    caddc
    co
    #
    @3
    cfzo
    co
    #
    wral
    #
    wa
    #
    vp
    cprime
    wrex
    #
    cN
    vn
    prmunb
    @0
    @2
    @11
    vn
    cprime
    @0
    @1
    cprime
    wcel
    #
    @2
    w3a
    #
    @3
    @5
    cle
    wbr
    #
    vz
    cN
    vq
    cv
    #
    clt
    wbr
    #
    @15
    @1
    cle
    wbr
    #
    wa
    #
    vq
    cprime
    crab
    #
    wral
    #
    vp
    @19
    wrex
    @11
    vp
    vz
    @19
    @1
    cN
    vq
    @19
    eqid
    prmgaplem4
    @13
    @20
    @10
    vp
    @19
    cprime
    @13
    @3
    @19
    wcel
    #
    @20
    @3
    cprime
    wcel
    #
    @10
    wa
    #
    @21
    @22
    @4
    @3
    @1
    cle
    wbr
    #
    wa
    #
    wa
    #
    @13
    @20
    @23
    wi
    #
    @18
    @25
    vq
    @3
    cprime
    @15
    @3
    wceq
    @16
    @4
    @17
    @24
    @15
    @3
    cN
    clt
    breq2
    @15
    @3
    @1
    cle
    breq1
    anbi12d
    elrab
    @13
    @26
    @27
    @13
    @26
    wa
    #
    @20
    @23
    @28
    @20
    wa
    @22
    @4
    @9
    @13
    @22
    @25
    @20
    simplrl
    @28
    @4
    @20
    @13
    @22
    @4
    @24
    simprrl
    adantr
    @28
    @20
    @9
    @28
    @14
    @6
    vz
    @19
    @8
    @5
    cprime
    wcel
    #
    @28
    @5
    @19
    wcel
    #
    @14
    wi
    #
    @5
    @8
    wcel
    #
    @6
    wi
    #
    wi
    #
    wi
    #
    @29
    @28
    @34
    @29
    @28
    wa
    #
    @32
    @31
    @6
    @36
    @32
    @31
    @6
    wi
    @36
    @32
    wa
    #
    @30
    @14
    @6
    @37
    @29
    cN
    @5
    clt
    wbr
    #
    @5
    @1
    cle
    wbr
    #
    wa
    #
    @30
    @29
    @28
    @32
    simpll
    @32
    @36
    @40
    @32
    @5
    @7
    cuz
    cfv
    wcel
    #
    @3
    cz
    wcel
    #
    @5
    @3
    clt
    wbr
    #
    w3a
    @36
    @40
    wi
    #
    @5
    @7
    @3
    elfzo2
    @41
    @42
    @43
    @44
    @41
    @7
    cz
    wcel
    #
    @5
    cz
    wcel
    #
    @7
    @5
    cle
    wbr
    #
    w3a
    @42
    @43
    @44
    wi
    wi
    #
    @7
    @5
    eluz2
    @47
    @45
    @48
    @46
    @47
    @42
    @43
    @36
    @40
    @47
    @42
    wa
    #
    @43
    wa
    #
    @36
    wa
    @38
    @39
    @50
    @36
    @38
    @49
    @36
    @38
    wi
    #
    @43
    @47
    @51
    @42
    @36
    @47
    @38
    @28
    @29
    @47
    @38
    wi
    #
    @13
    @29
    @52
    wi
    #
    @26
    @0
    @12
    @53
    @2
    @0
    @29
    @38
    @47
    @0
    cN
    cz
    wcel
    @46
    @38
    @47
    wb
    @29
    cN
    nnz
    @5
    prmz
    cN
    @5
    zltp1le
    syl2an
    exbiri
    3ad2ant1
    adantr
    impcom
    com12
    adantr
    adantr
    imp
    @36
    @50
    @39
    @36
    @43
    @39
    @49
    @28
    @29
    @43
    @39
    wi
    #
    @26
    @13
    @29
    @54
    wi
    #
    @25
    @22
    @13
    @55
    wi
    #
    @24
    @22
    @56
    wi
    @4
    @29
    @22
    @13
    @24
    @54
    @29
    @22
    @13
    @43
    @24
    @39
    @13
    @29
    @22
    @43
    @24
    @39
    wi
    wi
    #
    @12
    @0
    @29
    @22
    wa
    #
    @57
    wi
    @2
    @12
    @58
    @43
    @24
    @39
    @12
    @58
    wa
    @5
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    @43
    @24
    wa
    @39
    wi
    @29
    @59
    @12
    @22
    @29
    @5
    @5
    prmnn
    nnred
    #
    ad2antrl
    @58
    @60
    @12
    @22
    @60
    @29
    @22
    @3
    @3
    prmnn
    nnred
    #
    adantl
    adantl
    @12
    @61
    @58
    @12
    @1
    @1
    prmnn
    nnred
    adantr
    @5
    @3
    @1
    ltleletr
    syl3anc
    exp4b
    3ad2ant2
    expdcom
    com45
    com14
    adantl
    impcom
    impcom
    impcom
    adantld
    impcom
    jca
    exp41
    3ad2ant3
    sylbi
    3imp
    sylbi
    impcom
    @18
    @40
    vq
    @5
    cprime
    @15
    @5
    wceq
    @16
    @38
    @17
    @39
    @15
    @5
    cN
    clt
    breq2
    @15
    @5
    @1
    cle
    breq1
    anbi12d
    elrab
    sylanbrc
    @32
    @36
    @43
    @14
    @6
    wi
    @5
    @7
    @3
    elfzolt2
    @36
    @43
    wa
    @14
    @6
    @36
    @43
    @14
    wn
    #
    @29
    @59
    @60
    @43
    @64
    wi
    @28
    @62
    @22
    @60
    @13
    @25
    @63
    ad2antrl
    @59
    @60
    wa
    @43
    @64
    @5
    @3
    ltnle
    biimpd
    syl2an
    imp
    pm2.21d
    sylan2
    embantd
    ex
    com23
    ex
    @29
    wn
    @6
    @35
    @5
    cprime
    df-nel
    @6
    @34
    @28
    @6
    @33
    @31
    @6
    @32
    ax-1
    a1d
    a1d
    sylbir
    pm2.61i
    ralimdv2
    imp
    jca32
    ex
    ex
    syl5bi
    impd
    reximdv2
    mpd
    rexlimdv3a
    mpd
end
