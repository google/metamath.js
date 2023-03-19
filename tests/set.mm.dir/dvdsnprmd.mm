include "cdvds.mm"
include "wbr.mm"
include "cprime.mm"
include "wcel.mm"
include "wn.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "wa.mm"
include "wb.mm"
include "dvdszrcl.mm"
include "divides.mm"
include "3syl.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "cle.mm"
include "2z.mm"
include "a1i.mm"
include "simplr.mm"
include "c1.mm"
include "clt.mm"
include "adantr.mm"
include "breq2.mm"
include "adantl.mm"
include "mpbird.mm"
include "cr.mm"
include "cc0.mm"
include "w3a.mm"
include "wi.mm"
include "zre.mm"
include "3ad2ant1.mm"
include "3ad2ant3.mm"
include "0lt1.mm"
include "0red.mm"
include "1red.mm"
include "lttr.mm"
include "syl3anc.mm"
include "mpani.mm"
include "imp.mm"
include "3adant3.mm"
include "3jca.mm"
include "3exp.mm"
include "mpd.mm"
include "ltmulgt12.mm"
include "syl.mm"
include "caddc.mm"
include "df-2.mm"
include "breq1i.mm"
include "1zzd.mm"
include "zltp1le.mm"
include "mpancom.mm"
include "bicomd.mm"
include "syl5bb.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "simpl.mm"
include "biimpa.mm"
include "sylibr.mm"
include "ex.mm"
include "nprm.mm"
include "syl2anc.mm"
include "eleq1.mm"
include "notbid.mm"
include "mpbid.mm"
include "rexlimdva.mm"
include "sylbid.mm"

theorem dvdsnprmd
  let wph: wff ph
  let cA: class A
  let cN: class N
  let vk: setvar k
  assume dvdsnprmd.g: |- ( ph -> 1 < A )
  assume dvdsnprmd.l: |- ( ph -> A < N )
  assume dvdsnprmd.d: |- ( ph -> A || N )


  assert |- ( ph -> -. N e. Prime )

  proof
    wph
    cA
    cN
    cdvds
    wbr
    #
    cN
    cprime
    wcel
    #
    wn
    #
    dvdsnprmd.d
    wph
    @0
    vk
    cv
    #
    cA
    cmul
    co
    #
    cN
    wceq
    #
    vk
    cz
    wrex
    #
    @2
    wph
    @0
    cA
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    @0
    @6
    wb
    dvdsnprmd.d
    cA
    cN
    dvdszrcl
    #
    vk
    cA
    cN
    divides
    3syl
    wph
    @5
    @2
    vk
    cz
    wph
    @3
    cz
    wcel
    #
    wa
    #
    @5
    @2
    @12
    @5
    wa
    #
    @4
    cprime
    wcel
    #
    wn
    #
    @2
    @13
    @3
    c2
    cuz
    cfv
    #
    wcel
    #
    cA
    @16
    wcel
    #
    @15
    @13
    c2
    cz
    wcel
    #
    @11
    c2
    @3
    cle
    wbr
    #
    @17
    @19
    @13
    2z
    a1i
    wph
    @11
    @5
    simplr
    @13
    @20
    c1
    @3
    clt
    wbr
    #
    @13
    @21
    cA
    @4
    clt
    wbr
    #
    @13
    @22
    cA
    cN
    clt
    wbr
    #
    @12
    @23
    @5
    wph
    @23
    @11
    dvdsnprmd.l
    adantr
    adantr
    @5
    @22
    @23
    wb
    @12
    @4
    cN
    cA
    clt
    breq2
    adantl
    mpbird
    @13
    cA
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    w3a
    #
    @21
    @22
    wb
    @12
    @27
    @5
    wph
    @11
    @27
    wph
    c1
    cA
    clt
    wbr
    #
    @11
    @27
    wi
    #
    dvdsnprmd.g
    wph
    @0
    @9
    @28
    @29
    wi
    #
    dvdsnprmd.d
    @10
    @7
    @30
    @8
    @7
    @28
    @11
    @27
    @7
    @28
    @11
    w3a
    @24
    @25
    @26
    @7
    @28
    @24
    @11
    cA
    zre
    #
    3ad2ant1
    @11
    @7
    @25
    @28
    @3
    zre
    3ad2ant3
    @7
    @28
    @26
    @11
    @7
    @28
    @26
    @7
    cc0
    c1
    clt
    wbr
    #
    @28
    @26
    0lt1
    @7
    cc0
    cr
    wcel
    c1
    cr
    wcel
    @24
    @32
    @28
    wa
    @26
    wi
    @7
    0red
    @7
    1red
    @31
    cc0
    c1
    cA
    lttr
    syl3anc
    mpani
    imp
    3adant3
    3jca
    3exp
    adantr
    3syl
    mpd
    imp
    adantr
    cA
    @3
    ltmulgt12
    syl
    mpbird
    @20
    c1
    c1
    caddc
    co
    #
    @3
    cle
    wbr
    #
    @13
    @21
    c2
    @33
    @3
    cle
    df-2
    breq1i
    @12
    @34
    @21
    wb
    #
    @5
    @11
    @35
    wph
    @11
    @21
    @34
    c1
    cz
    wcel
    #
    @11
    @21
    @34
    wb
    @11
    1zzd
    c1
    @3
    zltp1le
    mpancom
    bicomd
    adantl
    adantr
    syl5bb
    mpbird
    c2
    @3
    eluz2
    syl3anbrc
    @12
    @18
    @5
    wph
    @18
    @11
    wph
    @19
    @7
    c2
    cA
    cle
    wbr
    #
    w3a
    #
    @18
    wph
    @28
    @38
    dvdsnprmd.g
    wph
    @0
    @9
    @28
    @38
    wi
    #
    dvdsnprmd.d
    @10
    @7
    @39
    @8
    @7
    @28
    @38
    @7
    @28
    wa
    #
    @19
    @7
    @37
    @19
    @40
    2z
    a1i
    @7
    @28
    simpl
    @40
    @33
    cA
    cle
    wbr
    #
    @37
    @7
    @28
    @41
    @36
    @7
    @28
    @41
    wb
    @7
    1zzd
    c1
    cA
    zltp1le
    mpancom
    biimpa
    c2
    @33
    cA
    cle
    df-2
    breq1i
    sylibr
    3jca
    ex
    adantr
    3syl
    mpd
    c2
    cA
    eluz2
    sylibr
    adantr
    adantr
    @3
    cA
    nprm
    syl2anc
    @5
    @15
    @2
    wb
    @12
    @5
    @14
    @1
    @4
    cN
    cprime
    eleq1
    notbid
    adantl
    mpbid
    ex
    rexlimdva
    sylbid
    mpd
end
