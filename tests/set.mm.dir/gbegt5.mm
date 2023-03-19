include "cgbe.mm"
include "wcel.mm"
include "ceven.mm"
include "cv.mm"
include "codd.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cprime.mm"
include "wrex.mm"
include "wa.mm"
include "c5.mm"
include "clt.mm"
include "wbr.mm"
include "isgbe.mm"
include "wi.mm"
include "c3.mm"
include "cuz.mm"
include "cfv.mm"
include "oddprmuzge3.mm"
include "ancoms.mm"
include "cz.mm"
include "cle.mm"
include "eluz2.mm"
include "cr.mm"
include "zre.mm"
include "3re.mm"
include "pm3.2i.mm"
include "pm3.22.mm"
include "le2add.mm"
include "sylancr.mm"
include "ancomsd.mm"
include "c6.mm"
include "3p3e6.mm"
include "breq1i.mm"
include "5lt6.mm"
include "5re.mm"
include "a1i.mm"
include "6re.mm"
include "readdcl.mm"
include "ltletr.mm"
include "syl3anc.mm"
include "mpani.mm"
include "syl5bi.mm"
include "syld.mm"
include "syl2an.mm"
include "ex.mm"
include "adantl.mm"
include "com23.mm"
include "exp4b.mm"
include "3imp.mm"
include "com13.mm"
include "imp.mm"
include "3adant1.mm"
include "sylbi.mm"
include "an4s.mm"
include "3adant3.mm"
include "impcom.mm"
include "wb.mm"
include "breq2.mm"
include "3ad2ant3.mm"
include "mpbird.mm"
include "rexlimdvv.mm"

theorem gbegt5
  let cZ: class Z
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. GoldbachEven -> 5 < Z )

  proof
    cZ
    cgbe
    wcel
    cZ
    ceven
    wcel
    #
    vp
    cv
    #
    codd
    wcel
    #
    vq
    cv
    #
    codd
    wcel
    #
    cZ
    @1
    @3
    caddc
    co
    #
    wceq
    #
    w3a
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
    vq
    vp
    isgbe
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
    @3
    cprime
    wcel
    #
    wa
    #
    @7
    @9
    wi
    wi
    @0
    @12
    @7
    @9
    @12
    @7
    wa
    @9
    c5
    @5
    clt
    wbr
    #
    @7
    @12
    @13
    @2
    @4
    @12
    @13
    wi
    @6
    @2
    @4
    wa
    @12
    @13
    @2
    @10
    @4
    @11
    @13
    @2
    @10
    wa
    @1
    c3
    cuz
    cfv
    #
    wcel
    #
    @3
    @14
    wcel
    #
    @13
    @4
    @11
    wa
    @10
    @2
    @15
    @1
    oddprmuzge3
    ancoms
    @11
    @4
    @16
    @3
    oddprmuzge3
    ancoms
    @15
    @16
    @13
    @15
    c3
    cz
    wcel
    #
    @1
    cz
    wcel
    #
    c3
    @1
    cle
    wbr
    #
    w3a
    #
    @16
    @13
    wi
    c3
    @1
    eluz2
    @16
    @17
    @3
    cz
    wcel
    #
    c3
    @3
    cle
    wbr
    #
    w3a
    #
    @20
    @13
    c3
    @3
    eluz2
    @18
    @19
    @23
    @13
    wi
    #
    @17
    @18
    @19
    @24
    @23
    @19
    @18
    @13
    @17
    @21
    @22
    @19
    @18
    @13
    wi
    #
    wi
    @17
    @21
    @22
    @19
    @25
    @17
    @21
    wa
    @18
    @22
    @19
    wa
    #
    @13
    @21
    @18
    @26
    @13
    wi
    #
    wi
    @17
    @21
    @18
    @27
    @21
    @3
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    @27
    @18
    @3
    zre
    @1
    zre
    @28
    @29
    wa
    #
    @26
    c3
    c3
    caddc
    co
    #
    @5
    cle
    wbr
    #
    @13
    @30
    @19
    @22
    @32
    @30
    c3
    cr
    wcel
    #
    @33
    wa
    @29
    @28
    wa
    @19
    @22
    wa
    @32
    wi
    @33
    @33
    3re
    3re
    pm3.2i
    @28
    @29
    pm3.22
    c3
    c3
    @1
    @3
    le2add
    sylancr
    ancomsd
    @32
    c6
    @5
    cle
    wbr
    #
    @30
    @13
    @31
    c6
    @5
    cle
    3p3e6
    breq1i
    @30
    c5
    c6
    clt
    wbr
    #
    @34
    @13
    5lt6
    @30
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
    #
    @35
    @34
    wa
    @13
    wi
    @36
    @30
    5re
    a1i
    @37
    @30
    6re
    a1i
    @29
    @28
    @38
    @1
    @3
    readdcl
    ancoms
    c5
    c6
    @5
    ltletr
    syl3anc
    mpani
    syl5bi
    syld
    syl2an
    ex
    adantl
    com23
    exp4b
    3imp
    com13
    imp
    3adant1
    syl5bi
    sylbi
    imp
    syl2an
    an4s
    ex
    3adant3
    impcom
    @7
    @9
    @13
    wb
    #
    @12
    @6
    @2
    @39
    @4
    cZ
    @5
    c5
    clt
    breq2
    3ad2ant3
    adantl
    mpbird
    ex
    a1i
    rexlimdvv
    imp
    sylbi
end
