include "cprime.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "c1.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "cn.mm"
include "wral.mm"
include "wa.mm"
include "wn.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "isprm2.mm"
include "iman.mm"
include "wb.mm"
include "clt.mm"
include "cle.mm"
include "eluz2nn.mm"
include "cz.mm"
include "nnz.mm"
include "dvdsle.mm"
include "sylan.mm"
include "nnge1.mm"
include "adantr.mm"
include "jctild.mm"
include "sylan2.mm"
include "wne.mm"
include "cr.mm"
include "zre.mm"
include "nnre.mm"
include "1re.mm"
include "leltne.mm"
include "mp3an1.mm"
include "3adant2.mm"
include "3expia.mm"
include "anim12d.mm"
include "syl2an.mm"
include "pm4.38.mm"
include "df-ne.mm"
include "nesym.mm"
include "anbi12i.mm"
include "ioran.mm"
include "bitr4i.mm"
include "syl6bb.mm"
include "syl6.mm"
include "syld.mm"
include "imp.mm"
include "eluzelz.mm"
include "caddc.mm"
include "1z.mm"
include "zltp1le.mm"
include "mpan.mm"
include "df-2.mm"
include "breq1i.mm"
include "syl6bbr.mm"
include "zltlem1.mm"
include "anbi12d.mm"
include "peano2zm.mm"
include "2z.mm"
include "elfz.mm"
include "mp3an2.mm"
include "bitr4d.mm"
include "bitr3d.mm"
include "anasss.mm"
include "expcom.mm"
include "pm5.32d.mm"
include "fzssuz.mm"
include "wss.mm"
include "2eluzge1.mm"
include "uzss.mm"
include "ax-mp.mm"
include "sstri.mm"
include "nnuz.mm"
include "sseqtr4i.mm"
include "sseli.mm"
include "pm4.71ri.mm"
include "notbid.mm"
include "syl5bb.mm"
include "pm5.74da.mm"
include "bi2.04.mm"
include "con2b.mm"
include "3bitr3g.mm"
include "ralbidv2.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem isprm3
  let vz: setvar z
  let cP: class P
  let vn: setvar n

  disjoint P z
  disjoint n z
  disjoint P n
  assert |- ( P e. Prime <-> ( P e. ( ZZ>= ` 2 ) /\ A. z e. ( 2 ... ( P - 1 ) ) -. z || P ) )

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
    cP
    cdvds
    wbr
    #
    @2
    c1
    wceq
    #
    @2
    cP
    wceq
    #
    wo
    #
    wi
    #
    vz
    cn
    wral
    #
    wa
    @1
    @3
    wn
    #
    vz
    c2
    cP
    c1
    cmin
    co
    #
    cfz
    co
    #
    wral
    #
    wa
    vz
    cP
    isprm2
    @1
    @8
    @12
    @1
    @7
    @9
    vz
    cn
    @11
    @1
    @3
    @2
    cn
    wcel
    #
    @6
    wi
    #
    wi
    @3
    @2
    @11
    wcel
    #
    wn
    #
    wi
    @13
    @7
    wi
    @15
    @9
    wi
    @1
    @3
    @14
    @16
    @14
    @13
    @6
    wn
    #
    wa
    #
    wn
    @1
    @3
    wa
    #
    @16
    @13
    @6
    iman
    @19
    @18
    @15
    @19
    @18
    @13
    @15
    wa
    @15
    @19
    @13
    @17
    @15
    @13
    @19
    @17
    @15
    wb
    #
    @13
    @1
    @3
    @20
    @13
    @1
    wa
    #
    @3
    wa
    c1
    @2
    clt
    wbr
    #
    @2
    cP
    clt
    wbr
    #
    wa
    #
    @17
    @15
    @21
    @3
    @24
    @17
    wb
    #
    @21
    @3
    c1
    @2
    cle
    wbr
    #
    @2
    cP
    cle
    wbr
    #
    wa
    #
    @25
    @1
    @13
    cP
    cn
    wcel
    #
    @3
    @28
    wi
    cP
    eluz2nn
    #
    @13
    @29
    wa
    @3
    @27
    @26
    @13
    @2
    cz
    wcel
    #
    @29
    @3
    @27
    wi
    @2
    nnz
    #
    @2
    cP
    dvdsle
    sylan
    @13
    @26
    @29
    @2
    nnge1
    adantr
    jctild
    sylan2
    @13
    @31
    @29
    @28
    @25
    wi
    @1
    @32
    @30
    @31
    @29
    wa
    @28
    @22
    @2
    c1
    wne
    #
    wb
    #
    @23
    cP
    @2
    wne
    #
    wb
    #
    wa
    #
    @25
    @31
    @2
    cr
    wcel
    #
    cP
    cr
    wcel
    #
    @28
    @37
    wi
    @29
    @2
    zre
    cP
    nnre
    @38
    @39
    wa
    @26
    @34
    @27
    @36
    @38
    @39
    @26
    @34
    @38
    @26
    @34
    @39
    c1
    cr
    wcel
    @38
    @26
    @34
    1re
    c1
    @2
    leltne
    mp3an1
    3adant2
    3expia
    @38
    @39
    @27
    @36
    @2
    cP
    leltne
    3expia
    anim12d
    syl2an
    @37
    @24
    @33
    @35
    wa
    #
    @17
    @22
    @23
    @33
    @35
    pm4.38
    @40
    @4
    wn
    #
    @5
    wn
    #
    wa
    @17
    @33
    @41
    @35
    @42
    @2
    c1
    df-ne
    cP
    @2
    nesym
    anbi12i
    @4
    @5
    ioran
    bitr4i
    syl6bb
    syl6
    syl2an
    syld
    imp
    @21
    @24
    @15
    wb
    #
    @3
    @13
    @31
    cP
    cz
    wcel
    #
    @43
    @1
    @32
    c2
    cP
    eluzelz
    @31
    @44
    wa
    #
    @24
    c2
    @2
    cle
    wbr
    #
    @2
    @10
    cle
    wbr
    #
    wa
    #
    @15
    @45
    @22
    @46
    @23
    @47
    @31
    @22
    @46
    wb
    @44
    @31
    @22
    c1
    c1
    caddc
    co
    #
    @2
    cle
    wbr
    #
    @46
    c1
    cz
    wcel
    @31
    @22
    @50
    wb
    1z
    c1
    @2
    zltp1le
    mpan
    c2
    @49
    @2
    cle
    df-2
    breq1i
    syl6bbr
    adantr
    @2
    cP
    zltlem1
    anbi12d
    @44
    @31
    @10
    cz
    wcel
    #
    @15
    @48
    wb
    #
    cP
    peano2zm
    @31
    c2
    cz
    wcel
    @51
    @52
    2z
    @2
    c2
    @10
    elfz
    mp3an2
    sylan2
    bitr4d
    syl2an
    adantr
    bitr3d
    anasss
    expcom
    pm5.32d
    @15
    @13
    @11
    cn
    @2
    @11
    c1
    cuz
    cfv
    #
    cn
    @11
    @0
    @53
    c2
    @10
    fzssuz
    c2
    @53
    wcel
    @0
    @53
    wss
    2eluzge1
    c1
    c2
    uzss
    ax-mp
    sstri
    nnuz
    sseqtr4i
    sseli
    pm4.71ri
    syl6bbr
    notbid
    syl5bb
    pm5.74da
    @3
    @13
    @6
    bi2.04
    @3
    @15
    con2b
    3bitr3g
    ralbidv2
    pm5.32i
    bitri
end
