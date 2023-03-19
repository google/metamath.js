include "cgrp.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cfv.mm"
include "cgcd.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "cc0.mm"
include "wa.mm"
include "cc.mm"
include "cn0.mm"
include "mulgcl.mm"
include "3com23.mm"
include "odcl.mm"
include "syl.mm"
include "nn0cnd.mm"
include "adantr.mm"
include "mul02d.mm"
include "simpr.mm"
include "oveq1d.mm"
include "wb.mm"
include "simp3.mm"
include "3ad2ant2.mm"
include "nn0zd.mm"
include "gcdeq0.mm"
include "syl2anc.mm"
include "simplbda.mm"
include "3eqtr4rd.mm"
include "wne.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wral.mm"
include "simpll3.mm"
include "ad2antrr.mm"
include "gcddvds.mm"
include "simprd.mm"
include "wi.mm"
include "gcdcld.mm"
include "nn0z.mm"
include "adantl.mm"
include "dvdstr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "muldvds1.mm"
include "wrex.mm"
include "dvdszrcl.mm"
include "divides.mm"
include "ibi.mm"
include "simprr.mm"
include "adantrr.mm"
include "simprl.mm"
include "dvdscmulr.mm"
include "syl112anc.mm"
include "odmulgid.mm"
include "adantrl.mm"
include "simpl3.mm"
include "dvdsmulgcd.mm"
include "3bitrrd.mm"
include "zcnd.mm"
include "mulcomd.mm"
include "breq2d.mm"
include "bitrd.mm"
include "anassrs.mm"
include "breq2.mm"
include "bibi12d.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "syl5.mm"
include "pm5.21ndd.mm"
include "ralrimiva.mm"
include "nn0mulcld.mm"
include "dvdsext.mm"
include "mpbird.mm"
include "pm2.61dane.mm"

theorem odmulg
  let cA: class A
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cO: class O
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume odmulgid.1: |- X = ( Base ` G )
  assume odmulgid.2: |- O = ( od ` G )
  assume odmulgid.3: |- .x. = ( .g ` G )


  assert |- ( ( G e. Grp /\ A e. X /\ N e. ZZ ) -> ( O ` A ) = ( ( N gcd ( O ` A ) ) x. ( O ` ( N .x. A ) ) ) )

  proof
    cG
    cgrp
    wcel
    #
    cA
    cX
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cA
    cO
    cfv
    #
    cN
    @4
    cgcd
    co
    #
    cN
    cA
    c.x
    co
    #
    cO
    cfv
    #
    cmul
    co
    #
    wceq
    #
    @5
    cc0
    @3
    @5
    cc0
    wceq
    #
    wa
    #
    cc0
    @7
    cmul
    co
    cc0
    @8
    @4
    @11
    @7
    @3
    @7
    cc
    wcel
    @10
    @3
    @7
    @3
    @6
    cX
    wcel
    #
    @7
    cn0
    wcel
    #
    @0
    @2
    @1
    @12
    cX
    c.x
    cG
    cN
    cA
    odmulgid.1
    odmulgid.3
    mulgcl
    3com23
    @6
    cG
    cO
    cX
    odmulgid.1
    odmulgid.2
    odcl
    syl
    #
    nn0cnd
    adantr
    mul02d
    @11
    @5
    cc0
    @7
    cmul
    @3
    @10
    simpr
    oveq1d
    @3
    @10
    cN
    cc0
    wceq
    #
    @4
    cc0
    wceq
    #
    @3
    @2
    @4
    cz
    wcel
    #
    @10
    @15
    @16
    wa
    wb
    @0
    @1
    @2
    simp3
    #
    @3
    @4
    @1
    @0
    @4
    cn0
    wcel
    #
    @2
    cA
    cG
    cO
    cX
    odmulgid.1
    odmulgid.2
    odcl
    3ad2ant2
    #
    nn0zd
    #
    cN
    @4
    gcdeq0
    syl2anc
    simplbda
    3eqtr4rd
    @3
    @5
    cc0
    wne
    #
    wa
    #
    @9
    @4
    vx
    cv
    #
    cdvds
    wbr
    #
    @8
    @24
    cdvds
    wbr
    #
    wb
    #
    vx
    cn0
    wral
    #
    @23
    @27
    vx
    cn0
    @23
    @24
    cn0
    wcel
    #
    wa
    #
    @5
    @24
    cdvds
    wbr
    #
    @25
    @26
    @30
    @5
    @4
    cdvds
    wbr
    #
    @25
    @31
    @30
    @5
    cN
    cdvds
    wbr
    #
    @32
    @30
    @2
    @17
    @33
    @32
    wa
    @0
    @1
    @2
    @22
    @29
    simpll3
    @3
    @17
    @22
    @29
    @21
    ad2antrr
    #
    cN
    @4
    gcddvds
    syl2anc
    simprd
    @30
    @5
    cz
    wcel
    #
    @17
    @24
    cz
    wcel
    #
    @32
    @25
    wa
    @31
    wi
    @23
    @35
    @29
    @23
    @5
    @3
    @5
    cn0
    wcel
    @22
    @3
    cN
    @4
    @18
    @21
    gcdcld
    adantr
    #
    nn0zd
    #
    adantr
    #
    @34
    @29
    @36
    @23
    @24
    nn0z
    adantl
    #
    @5
    @4
    @24
    dvdstr
    syl3anc
    mpand
    @30
    @35
    @7
    cz
    wcel
    #
    @36
    @26
    @31
    wi
    @39
    @3
    @41
    @22
    @29
    @3
    @7
    @14
    nn0zd
    #
    ad2antrr
    @40
    @5
    @7
    @24
    muldvds1
    syl3anc
    @23
    @31
    @27
    wi
    @29
    @31
    vy
    cv
    #
    @5
    cmul
    co
    #
    @24
    wceq
    #
    vy
    cz
    wrex
    #
    @23
    @27
    @31
    @46
    @31
    @35
    @36
    wa
    @31
    @46
    wb
    @5
    @24
    dvdszrcl
    vy
    @5
    @24
    divides
    syl
    ibi
    @23
    @45
    @27
    vy
    cz
    @23
    @43
    cz
    wcel
    #
    wa
    @4
    @44
    cdvds
    wbr
    #
    @8
    @44
    cdvds
    wbr
    #
    wb
    #
    @45
    @27
    @3
    @22
    @47
    @50
    @3
    @22
    @47
    wa
    #
    wa
    #
    @48
    @8
    @5
    @43
    cmul
    co
    #
    cdvds
    wbr
    #
    @49
    @52
    @54
    @7
    @43
    cdvds
    wbr
    #
    @4
    @43
    cN
    cmul
    co
    cdvds
    wbr
    #
    @48
    @52
    @41
    @47
    @35
    @22
    @54
    @55
    wb
    @3
    @41
    @51
    @42
    adantr
    @3
    @22
    @47
    simprr
    #
    @3
    @22
    @35
    @47
    @38
    adantrr
    #
    @3
    @22
    @47
    simprl
    @5
    @7
    @43
    dvdscmulr
    syl112anc
    @3
    @47
    @55
    @56
    wb
    @22
    cA
    c.x
    cG
    @43
    cN
    cO
    cX
    odmulgid.1
    odmulgid.2
    odmulgid.3
    odmulgid
    adantrl
    @52
    @47
    @2
    @56
    @48
    wb
    @57
    @0
    @1
    @2
    @51
    simpl3
    @4
    @43
    cN
    dvdsmulgcd
    syl2anc
    3bitrrd
    @52
    @53
    @44
    @8
    cdvds
    @52
    @5
    @43
    @52
    @5
    @58
    zcnd
    @52
    @43
    @57
    zcnd
    mulcomd
    breq2d
    bitrd
    anassrs
    @45
    @48
    @25
    @49
    @26
    @44
    @24
    @4
    cdvds
    breq2
    @44
    @24
    @8
    cdvds
    breq2
    bibi12d
    syl5ibcom
    rexlimdva
    syl5
    adantr
    pm5.21ndd
    ralrimiva
    @23
    @19
    @8
    cn0
    wcel
    @9
    @28
    wb
    @3
    @19
    @22
    @20
    adantr
    @23
    @5
    @7
    @37
    @3
    @13
    @22
    @14
    adantr
    nn0mulcld
    vx
    @4
    @8
    dvdsext
    syl2anc
    mpbird
    pm2.61dane
end
