include "cprime.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cdvds.mm"
include "wn.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "csqrt.mm"
include "cfl.mm"
include "cfz.mm"
include "cin.mm"
include "isprm5.mm"
include "cr.mm"
include "cc0.mm"
include "wb.mm"
include "prmz.mm"
include "zred.mm"
include "0red.mm"
include "c1.mm"
include "1red.mm"
include "clt.mm"
include "0lt1.mm"
include "a1i.mm"
include "prmgt1.mm"
include "lttrd.mm"
include "ltled.mm"
include "jca.mm"
include "eluzelre.mm"
include "2re.mm"
include "0le2.mm"
include "eluzle.mm"
include "letrd.mm"
include "resqcl.mm"
include "sqge0.mm"
include "adantr.mm"
include "sqrtle.mm"
include "sylan.mm"
include "sqrtsq.mm"
include "breq1d.mm"
include "bitrd.mm"
include "syl2anr.mm"
include "imbi1d.mm"
include "ralbidva.mm"
include "pm5.32i.mm"
include "impexp.mm"
include "cz.mm"
include "resqrtcld.mm"
include "flcld.mm"
include "anim12i.mm"
include "prmuz2.mm"
include "syl.mm"
include "ad2antlr.mm"
include "flge.mm"
include "syl2an.mm"
include "biimpa.mm"
include "2z.mm"
include "elfz4.mm"
include "mp3anl1.mm"
include "syl12anc.mm"
include "anasss.mm"
include "simprl.mm"
include "elind.mm"
include "ex.mm"
include "elin.mm"
include "elfzelz.mm"
include "adantl.mm"
include "reflcl.mm"
include "elfzle2.mm"
include "flle.mm"
include "anim1d.mm"
include "syl5bi.mm"
include "ancom.mm"
include "syl6ib.mm"
include "impbid.mm"
include "syl5bbr.mm"
include "ralbidv2.mm"
include "3bitri.mm"

theorem isprm7
  let vz: setvar z
  let cP: class P

  disjoint P z
  assert |- ( P e. Prime <-> ( P e. ( ZZ>= ` 2 ) /\ A. z e. ( ( 2 ... ( |_ ` ( sqrt ` P ) ) ) i^i Prime ) -. z || P ) )

  proof
    cP
    cprime
    wcel
    cP
    c2
    cuz
    cfv
    #
    wcel
    #
    vz
    cv
    #
    c2
    cexp
    co
    #
    cP
    cle
    wbr
    #
    @2
    cP
    cdvds
    wbr
    wn
    #
    wi
    #
    vz
    cprime
    wral
    #
    wa
    @1
    @2
    cP
    csqrt
    cfv
    #
    cle
    wbr
    #
    @5
    wi
    #
    vz
    cprime
    wral
    #
    wa
    @1
    @5
    vz
    c2
    @8
    cfl
    cfv
    #
    cfz
    co
    #
    cprime
    cin
    #
    wral
    #
    wa
    vz
    cP
    isprm5
    @1
    @7
    @11
    @1
    @6
    @10
    vz
    cprime
    @1
    @2
    cprime
    wcel
    #
    wa
    #
    @4
    @9
    @5
    @16
    @2
    cr
    wcel
    #
    cc0
    @2
    cle
    wbr
    #
    wa
    #
    cP
    cr
    wcel
    #
    cc0
    cP
    cle
    wbr
    #
    wa
    #
    @4
    @9
    wb
    @1
    @16
    @18
    @19
    @16
    @2
    @2
    prmz
    #
    zred
    #
    @16
    cc0
    @2
    @16
    0red
    #
    @25
    @16
    cc0
    c1
    @2
    @26
    @16
    1red
    @25
    cc0
    c1
    clt
    wbr
    @16
    0lt1
    a1i
    @2
    prmgt1
    lttrd
    ltled
    jca
    @1
    @21
    @22
    c2
    cP
    eluzelre
    #
    @1
    cc0
    c2
    cP
    @1
    0red
    c2
    cr
    wcel
    @1
    2re
    a1i
    @27
    cc0
    c2
    cle
    wbr
    @1
    0le2
    a1i
    c2
    cP
    eluzle
    letrd
    #
    jca
    @20
    @23
    wa
    @4
    @3
    csqrt
    cfv
    #
    @8
    cle
    wbr
    #
    @9
    @20
    @3
    cr
    wcel
    #
    cc0
    @3
    cle
    wbr
    #
    wa
    #
    @23
    @4
    @30
    wb
    @18
    @33
    @19
    @18
    @31
    @32
    @2
    resqcl
    @2
    sqge0
    jca
    adantr
    @3
    cP
    sqrtle
    sylan
    @20
    @30
    @9
    wb
    @23
    @20
    @29
    @2
    @8
    cle
    @2
    sqrtsq
    breq1d
    adantr
    bitrd
    syl2anr
    imbi1d
    ralbidva
    pm5.32i
    @1
    @11
    @15
    @1
    @10
    @5
    vz
    cprime
    @14
    @16
    @10
    wi
    @16
    @9
    wa
    #
    @5
    wi
    @1
    @2
    @14
    wcel
    #
    @5
    wi
    @16
    @9
    @5
    impexp
    @1
    @34
    @35
    @5
    @1
    @34
    @35
    @1
    @34
    @35
    @1
    @34
    wa
    @13
    cprime
    @2
    @1
    @16
    @9
    @2
    @13
    wcel
    #
    @17
    @9
    wa
    @12
    cz
    wcel
    #
    @2
    cz
    wcel
    #
    wa
    #
    c2
    @2
    cle
    wbr
    #
    @2
    @12
    cle
    wbr
    #
    @36
    @17
    @39
    @9
    @1
    @37
    @16
    @38
    @1
    @8
    @1
    cP
    @27
    @28
    resqrtcld
    #
    flcld
    @24
    anim12i
    adantr
    @16
    @40
    @1
    @9
    @16
    @2
    @0
    wcel
    @40
    @2
    prmuz2
    c2
    @2
    eluzle
    syl
    ad2antlr
    @17
    @9
    @41
    @1
    @8
    cr
    wcel
    #
    @38
    @9
    @41
    wb
    @16
    @42
    @24
    @8
    @2
    flge
    syl2an
    biimpa
    c2
    cz
    wcel
    @37
    @38
    @40
    @41
    wa
    @36
    2z
    @2
    c2
    @12
    elfz4
    mp3anl1
    syl12anc
    anasss
    @1
    @16
    @9
    simprl
    elind
    ex
    @1
    @35
    @9
    @16
    wa
    #
    @34
    @35
    @36
    @16
    wa
    @1
    @44
    @2
    @13
    cprime
    elin
    @1
    @36
    @9
    @16
    @1
    @36
    @9
    @1
    @36
    wa
    @2
    @12
    @8
    @36
    @18
    @1
    @36
    @2
    @2
    c2
    @12
    elfzelz
    zred
    adantl
    @1
    @12
    cr
    wcel
    #
    @36
    @1
    @43
    @45
    @42
    @8
    reflcl
    syl
    adantr
    @1
    @43
    @36
    @42
    adantr
    @36
    @41
    @1
    @2
    c2
    @12
    elfzle2
    adantl
    @1
    @12
    @8
    cle
    wbr
    #
    @36
    @1
    @43
    @46
    @42
    @8
    flle
    syl
    adantr
    letrd
    ex
    anim1d
    syl5bi
    @9
    @16
    ancom
    syl6ib
    impbid
    imbi1d
    syl5bbr
    ralbidv2
    pm5.32i
    3bitri
end
