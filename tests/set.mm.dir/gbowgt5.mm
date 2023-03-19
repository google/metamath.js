include "cgbow.mm"
include "wcel.mm"
include "codd.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cprime.mm"
include "wrex.mm"
include "wa.mm"
include "c5.mm"
include "clt.mm"
include "wbr.mm"
include "isgbow.mm"
include "wi.mm"
include "c2.mm"
include "cz.mm"
include "cle.mm"
include "w3a.mm"
include "cuz.mm"
include "cfv.mm"
include "prmuz2.mm"
include "eluz2.mm"
include "sylib.mm"
include "anim12i.mm"
include "cr.mm"
include "zre.mm"
include "3ad2ant2.mm"
include "2re.mm"
include "pm3.2i.mm"
include "jctil.mm"
include "simp3.mm"
include "le2add.mm"
include "sylc.mm"
include "c4.mm"
include "2p2e4.mm"
include "breq1i.mm"
include "zaddcl.mm"
include "zred.mm"
include "adantr.mm"
include "4re.mm"
include "simpr.mm"
include "c6.mm"
include "4p2e6.mm"
include "5lt6.mm"
include "5re.mm"
include "a1i.mm"
include "6re.mm"
include "zaddcld.mm"
include "ltletr.mm"
include "syl3anc.mm"
include "mpani.mm"
include "syl5bi.mm"
include "expcom.mm"
include "com12.mm"
include "imp.mm"
include "mpd.mm"
include "exp31.mm"
include "breq2.mm"
include "syl5ibrcom.mm"
include "syl2an.mm"
include "rexlimdva.mm"
include "adantl.mm"
include "rexlimdvva.mm"
include "sylbi.mm"

theorem gbowgt5
  let cZ: class Z
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. GoldbachOddW -> 5 < Z )

  proof
    cZ
    cgbow
    wcel
    cZ
    codd
    wcel
    #
    cZ
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
    wa
    c5
    cZ
    clt
    wbr
    #
    cZ
    vr
    vq
    vp
    isgbow
    @0
    @8
    @9
    @0
    @7
    @9
    vp
    vq
    cprime
    cprime
    @1
    cprime
    wcel
    #
    @2
    cprime
    wcel
    #
    wa
    #
    @7
    @9
    wi
    @0
    @12
    @6
    @9
    vr
    cprime
    @12
    c2
    cz
    wcel
    #
    @1
    cz
    wcel
    #
    c2
    @1
    cle
    wbr
    #
    w3a
    #
    @13
    @2
    cz
    wcel
    #
    c2
    @2
    cle
    wbr
    #
    w3a
    #
    wa
    #
    @13
    @4
    cz
    wcel
    #
    c2
    @4
    cle
    wbr
    #
    w3a
    #
    @6
    @9
    wi
    @4
    cprime
    wcel
    #
    @10
    @16
    @11
    @19
    @10
    @1
    c2
    cuz
    cfv
    #
    wcel
    @16
    @1
    prmuz2
    c2
    @1
    eluz2
    sylib
    @11
    @2
    @25
    wcel
    @19
    @2
    prmuz2
    c2
    @2
    eluz2
    sylib
    anim12i
    @24
    @4
    @25
    wcel
    @23
    @4
    prmuz2
    c2
    @4
    eluz2
    sylib
    @20
    @23
    wa
    @9
    @6
    c5
    @5
    clt
    wbr
    #
    @20
    @23
    @26
    @20
    c2
    c2
    caddc
    co
    #
    @3
    cle
    wbr
    #
    @23
    @26
    wi
    #
    @20
    c2
    cr
    wcel
    #
    @30
    wa
    #
    @1
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    wa
    #
    wa
    @15
    @18
    wa
    @28
    @20
    @34
    @31
    @16
    @32
    @19
    @33
    @14
    @13
    @32
    @15
    @1
    zre
    3ad2ant2
    @17
    @13
    @33
    @18
    @2
    zre
    3ad2ant2
    anim12i
    @30
    @30
    2re
    2re
    pm3.2i
    jctil
    @16
    @15
    @19
    @18
    @13
    @14
    @15
    simp3
    @13
    @17
    @18
    simp3
    anim12i
    c2
    c2
    @1
    @2
    le2add
    sylc
    @16
    @19
    @28
    @29
    wi
    #
    @14
    @13
    @19
    @35
    wi
    @15
    @19
    @14
    @35
    @17
    @13
    @14
    @35
    wi
    @18
    @14
    @17
    @35
    @28
    c4
    @3
    cle
    wbr
    #
    @14
    @17
    wa
    #
    @29
    @27
    c4
    @3
    cle
    2p2e4
    breq1i
    @37
    @36
    @23
    @26
    @37
    @36
    wa
    #
    @23
    wa
    #
    c4
    c2
    caddc
    co
    #
    @5
    cle
    wbr
    #
    @26
    @39
    c4
    cr
    wcel
    #
    @30
    wa
    #
    @3
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    wa
    #
    wa
    @36
    @22
    wa
    @41
    @39
    @46
    @43
    @38
    @44
    @23
    @45
    @37
    @44
    @36
    @37
    @3
    @1
    @2
    zaddcl
    #
    zred
    adantr
    @21
    @13
    @45
    @22
    @4
    zre
    3ad2ant2
    anim12i
    @42
    @30
    4re
    2re
    pm3.2i
    jctil
    @38
    @36
    @23
    @22
    @37
    @36
    simpr
    @13
    @21
    @22
    simp3
    anim12i
    c4
    c2
    @3
    @4
    le2add
    sylc
    @38
    @23
    @41
    @26
    wi
    #
    @37
    @23
    @48
    wi
    @36
    @23
    @37
    @48
    @21
    @13
    @37
    @48
    wi
    @22
    @37
    @21
    @48
    @41
    c6
    @5
    cle
    wbr
    #
    @37
    @21
    wa
    #
    @26
    @40
    c6
    @5
    cle
    4p2e6
    breq1i
    @50
    c5
    c6
    clt
    wbr
    #
    @49
    @26
    5lt6
    @50
    c5
    cr
    wcel
    #
    c6
    cr
    wcel
    #
    @5
    cr
    wcel
    @51
    @49
    wa
    @26
    wi
    @52
    @50
    5re
    a1i
    @53
    @50
    6re
    a1i
    @50
    @5
    @50
    @3
    @4
    @37
    @3
    cz
    wcel
    @21
    @47
    adantr
    @37
    @21
    simpr
    zaddcld
    zred
    c5
    c6
    @5
    ltletr
    syl3anc
    mpani
    syl5bi
    expcom
    3ad2ant2
    com12
    adantr
    imp
    mpd
    exp31
    syl5bi
    expcom
    3ad2ant2
    com12
    3ad2ant2
    imp
    mpd
    imp
    cZ
    @5
    c5
    clt
    breq2
    syl5ibrcom
    syl2an
    rexlimdva
    adantl
    rexlimdvva
    imp
    sylbi
end
