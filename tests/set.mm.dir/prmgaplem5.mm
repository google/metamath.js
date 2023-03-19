include "c3.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cprime.mm"
include "crab.mm"
include "wral.mm"
include "wnel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfzo.mm"
include "wa.mm"
include "wrex.mm"
include "elrabi.mm"
include "ad2antlr.mm"
include "wceq.mm"
include "wb.mm"
include "breq1.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "raleqdv.mm"
include "anbi12d.mm"
include "adantl.mm"
include "elrab.mm"
include "simprbi.mm"
include "wi.mm"
include "cz.mm"
include "w3a.mm"
include "elfzo2.mm"
include "simpl.mm"
include "simpr3.mm"
include "sylanbrc.mm"
include "adantrl.mm"
include "eluz2.mm"
include "prmz.mm"
include "zltp1le.mm"
include "sylan.mm"
include "wn.mm"
include "cr.mm"
include "prmnn.mm"
include "nnred.mm"
include "zre.mm"
include "ltnle.mm"
include "biimpd.mm"
include "syl2an.mm"
include "pm2.21.mm"
include "syl6.mm"
include "sylbird.mm"
include "expcom.mm"
include "com23.mm"
include "a1i.mm"
include "3imp.mm"
include "sylbi.mm"
include "3ad2ant1.mm"
include "syl5com.mm"
include "imp.mm"
include "embantd.mm"
include "ex.mm"
include "df-nel.mm"
include "ax-1.mm"
include "a1d.mm"
include "sylbir.mm"
include "pm2.61i.mm"
include "impancom.mm"
include "syl5bi.mm"
include "ralimdv2.mm"
include "jca.mm"
include "rspcedvd.mm"
include "eqid.mm"
include "prmgaplem3.mm"
include "r19.29a.mm"

theorem prmgaplem5
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
  assert |- ( N e. ( ZZ>= ` 3 ) -> E. p e. Prime ( p < N /\ A. z e. ( ( p + 1 ) ..^ N ) z e/ Prime ) )

  proof
    cN
    c3
    cuz
    cfv
    wcel
    #
    vz
    cv
    #
    vr
    cv
    #
    cle
    wbr
    #
    vz
    vq
    cv
    #
    cN
    clt
    wbr
    #
    vq
    cprime
    crab
    #
    wral
    #
    vp
    cv
    #
    cN
    clt
    wbr
    #
    @1
    cprime
    wnel
    #
    vz
    @8
    c1
    caddc
    co
    #
    cN
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
    vr
    @6
    @0
    @2
    @6
    wcel
    #
    wa
    #
    @7
    wa
    #
    @14
    @2
    cN
    clt
    wbr
    #
    @10
    vz
    @2
    c1
    caddc
    co
    #
    cN
    cfzo
    co
    #
    wral
    #
    wa
    #
    vp
    @2
    cprime
    @15
    @2
    cprime
    wcel
    #
    @0
    @7
    @5
    vq
    @2
    cprime
    elrabi
    #
    ad2antlr
    @8
    @2
    wceq
    #
    @14
    @22
    wb
    @17
    @25
    @9
    @18
    @13
    @21
    @8
    @2
    cN
    clt
    breq1
    @25
    @10
    vz
    @12
    @20
    @25
    @11
    @19
    cN
    cfzo
    @8
    @2
    c1
    caddc
    oveq1
    oveq1d
    raleqdv
    anbi12d
    adantl
    @17
    @18
    @21
    @15
    @18
    @0
    @7
    @15
    @23
    @18
    @5
    @18
    vq
    @2
    cprime
    @4
    @2
    cN
    clt
    breq1
    elrab
    simprbi
    ad2antlr
    @16
    @7
    @21
    @16
    @3
    @10
    vz
    @6
    @20
    @16
    @1
    @6
    wcel
    #
    @3
    wi
    #
    @1
    @20
    wcel
    #
    @10
    wi
    @28
    @1
    @19
    cuz
    cfv
    wcel
    #
    cN
    cz
    wcel
    #
    @1
    cN
    clt
    wbr
    #
    w3a
    #
    @16
    @27
    wa
    @10
    @1
    @19
    cN
    elfzo2
    @16
    @32
    @27
    @10
    @1
    cprime
    wcel
    #
    @16
    @32
    wa
    #
    @27
    @10
    wi
    #
    wi
    #
    @33
    @34
    @35
    @33
    @34
    wa
    @26
    @3
    @10
    @33
    @32
    @26
    @16
    @33
    @32
    wa
    @33
    @31
    @26
    @33
    @32
    simpl
    @33
    @29
    @30
    @31
    simpr3
    @5
    @31
    vq
    @1
    cprime
    @4
    @1
    cN
    clt
    breq1
    elrab
    sylanbrc
    adantrl
    @34
    @3
    @10
    wi
    #
    @33
    @16
    @32
    @37
    @15
    @32
    @37
    wi
    @0
    @15
    @23
    @32
    @37
    @24
    @29
    @30
    @23
    @37
    wi
    #
    @31
    @29
    @19
    cz
    wcel
    #
    @1
    cz
    wcel
    #
    @19
    @1
    cle
    wbr
    #
    w3a
    @38
    @19
    @1
    eluz2
    @39
    @40
    @41
    @38
    @40
    @41
    @38
    wi
    wi
    @39
    @40
    @23
    @41
    @37
    @23
    @40
    @41
    @37
    wi
    @23
    @40
    wa
    #
    @41
    @2
    @1
    clt
    wbr
    #
    @37
    @23
    @2
    cz
    wcel
    @40
    @43
    @41
    wb
    @2
    prmz
    @2
    @1
    zltp1le
    sylan
    @42
    @43
    @3
    wn
    #
    @37
    @23
    @2
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    @43
    @44
    wi
    @40
    @23
    @2
    @2
    prmnn
    nnred
    @1
    zre
    @45
    @46
    wa
    @43
    @44
    @2
    @1
    ltnle
    biimpd
    syl2an
    @3
    @10
    pm2.21
    syl6
    sylbird
    expcom
    com23
    a1i
    3imp
    sylbi
    3ad2ant1
    syl5com
    adantl
    imp
    adantl
    embantd
    ex
    @33
    wn
    @10
    @36
    @1
    cprime
    df-nel
    @10
    @35
    @34
    @10
    @27
    ax-1
    a1d
    sylbir
    pm2.61i
    impancom
    syl5bi
    ex
    ralimdv2
    imp
    jca
    rspcedvd
    vr
    vz
    @6
    cN
    vq
    @6
    eqid
    prmgaplem3
    r19.29a
end
