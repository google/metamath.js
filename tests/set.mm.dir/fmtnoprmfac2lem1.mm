include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cprime.mm"
include "csn.mm"
include "cdif.mm"
include "cfmtno.mm"
include "cdvds.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "cmul.mm"
include "wceq.mm"
include "cn.mm"
include "wrex.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmo.mm"
include "eluz2nn.mm"
include "eldifi.mm"
include "id.mm"
include "fmtnoprmfac1.mm"
include "syl3an.mm"
include "wa.mm"
include "clgs.mm"
include "cz.mm"
include "2z.mm"
include "simp2.mm"
include "lgsvalmod.mm"
include "eqcomd.mm"
include "sylancr.mm"
include "ad2antrr.mm"
include "c8.mm"
include "c7.mm"
include "cpr.mm"
include "wi.mm"
include "cc.mm"
include "nncn.mm"
include "adantl.mm"
include "2nn.mm"
include "a1i.mm"
include "cn0.mm"
include "eluzge2nn0.mm"
include "peano2nn0.mm"
include "syl.mm"
include "nnexpcld.mm"
include "nncnd.mm"
include "adantr.mm"
include "mulcomd.mm"
include "8cn.mm"
include "cc0.mm"
include "wne.mm"
include "0re.mm"
include "8pos.mm"
include "gtneii.mm"
include "divcan2d.mm"
include "oveq1d.mm"
include "divcld.mm"
include "mulassd.mm"
include "3eqtrd.mm"
include "eqeq2d.mm"
include "oveq1.mm"
include "c3.mm"
include "cle.mm"
include "3m1e2.mm"
include "eluzle.mm"
include "syl5eqbr.mm"
include "cr.mm"
include "3re.mm"
include "1red.mm"
include "eluzelre.mm"
include "lesubaddd.mm"
include "mpbid.mm"
include "wb.mm"
include "3nn0.mm"
include "nn0sub.mm"
include "nnzd.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "cu2.mm"
include "eqcomi.mm"
include "2cnne0.mm"
include "eluzelz.mm"
include "peano2zd.mm"
include "3z.mm"
include "expsub.mm"
include "syl12anc.mm"
include "oveq12d.mm"
include "nnexpcl.mm"
include "mp2an.mm"
include "nncni.mm"
include "2cn.mm"
include "2ne0.mm"
include "expne0i.mm"
include "mp3an.mm"
include "eqtrd.mm"
include "rspcedvd.mm"
include "8nn.mm"
include "2nn0.mm"
include "nn0expcld.mm"
include "nn0zd.mm"
include "zdiv.mm"
include "nnz.mm"
include "zmulcld.mm"
include "nnzi.mm"
include "2re.mm"
include "8re.mm"
include "2lt8.mm"
include "ltleii.mm"
include "eluz2.mm"
include "mpbir3an.mm"
include "mulp1mod1.mm"
include "sylancl.mm"
include "1nn.mm"
include "prid1g.mm"
include "mp1i.mm"
include "eqeltrd.mm"
include "ex.mm"
include "sylbid.mm"
include "3ad2antl1.mm"
include "imp.mm"
include "2lgs.mm"
include "3ad2ant2.mm"
include "mpbird.mm"
include "clt.mm"
include "prmuz2.mm"
include "eluz2gt1.mm"
include "jca.mm"
include "1mod.mm"
include "3syl.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem fmtnoprmfac2lem1
  let cP: class P
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x


  assert |- ( ( N e. ( ZZ>= ` 2 ) /\ P e. ( Prime \ { 2 } ) /\ P || ( FermatNo ` N ) ) -> ( ( 2 ^ ( ( P - 1 ) / 2 ) ) mod P ) = 1 )

  proof
    cN
    c2
    cuz
    cfv
    #
    wcel
    #
    cP
    cprime
    c2
    csn
    #
    cdif
    wcel
    #
    cP
    cN
    cfmtno
    cfv
    cdvds
    wbr
    #
    w3a
    #
    cP
    vn
    cv
    #
    c2
    cN
    c1
    caddc
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    vn
    cn
    wrex
    #
    c2
    cP
    c1
    cmin
    co
    c2
    cdiv
    co
    cexp
    co
    cP
    cmo
    co
    #
    c1
    wceq
    #
    @1
    cN
    cn
    wcel
    @3
    cP
    cprime
    wcel
    #
    @4
    @4
    @12
    cN
    eluz2nn
    cP
    cprime
    @2
    eldifi
    #
    @4
    id
    cP
    vn
    cN
    fmtnoprmfac1
    syl3an
    @5
    @11
    @14
    vn
    cn
    @5
    @6
    cn
    wcel
    #
    wa
    #
    @11
    @14
    @18
    @11
    wa
    #
    @13
    c2
    cP
    clgs
    co
    #
    cP
    cmo
    co
    #
    c1
    cP
    cmo
    co
    #
    c1
    @5
    @13
    @21
    wceq
    #
    @17
    @11
    @5
    c2
    cz
    wcel
    #
    @3
    @23
    2z
    @1
    @3
    @4
    simp2
    @24
    @3
    wa
    @21
    @13
    c2
    cP
    lgsvalmod
    eqcomd
    sylancr
    ad2antrr
    @19
    @20
    c1
    cP
    cmo
    @19
    @20
    c1
    wceq
    #
    cP
    c8
    cmo
    co
    #
    c1
    c7
    cpr
    #
    wcel
    #
    @18
    @11
    @28
    @1
    @3
    @17
    @11
    @28
    wi
    @4
    @1
    @17
    wa
    #
    @11
    cP
    c8
    @8
    c8
    cdiv
    co
    #
    @6
    cmul
    co
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    @28
    @29
    @10
    @33
    cP
    @29
    @9
    @32
    c1
    caddc
    @29
    @9
    @8
    @6
    cmul
    co
    c8
    @30
    cmul
    co
    #
    @6
    cmul
    co
    @32
    @29
    @6
    @8
    @17
    @6
    cc
    wcel
    @1
    @6
    nncn
    adantl
    #
    @1
    @8
    cc
    wcel
    @17
    @1
    @8
    @1
    c2
    @7
    c2
    cn
    wcel
    #
    @1
    2nn
    a1i
    #
    @1
    cN
    cn0
    wcel
    @7
    cn0
    wcel
    #
    cN
    eluzge2nn0
    cN
    peano2nn0
    syl
    #
    nnexpcld
    nncnd
    #
    adantr
    #
    mulcomd
    @29
    @8
    @35
    @6
    cmul
    @29
    @35
    @8
    @29
    @8
    c8
    @42
    c8
    cc
    wcel
    #
    @29
    8cn
    a1i
    #
    c8
    cc0
    wne
    #
    @29
    cc0
    c8
    0re
    8pos
    gtneii
    #
    a1i
    divcan2d
    eqcomd
    oveq1d
    @29
    c8
    @30
    @6
    @44
    @1
    @30
    cc
    wcel
    @17
    @1
    @8
    c8
    @41
    @43
    @1
    8cn
    a1i
    @45
    @1
    @46
    a1i
    divcld
    adantr
    @36
    mulassd
    3eqtrd
    oveq1d
    eqeq2d
    @29
    @34
    @28
    @29
    @34
    wa
    @26
    @33
    c8
    cmo
    co
    #
    @27
    @34
    @26
    @47
    wceq
    @29
    cP
    @33
    c8
    cmo
    oveq1
    adantl
    @29
    @47
    @27
    wcel
    @34
    @29
    @47
    c1
    @27
    @29
    @31
    cz
    wcel
    c8
    @0
    wcel
    #
    @47
    c1
    wceq
    @29
    @30
    @6
    @1
    @30
    cz
    wcel
    #
    @17
    @1
    c8
    vk
    cv
    #
    cmul
    co
    #
    @8
    wceq
    #
    vk
    cz
    wrex
    #
    @49
    @1
    @52
    c8
    c2
    @7
    c3
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    @8
    wceq
    #
    vk
    @55
    cz
    @1
    @55
    @1
    c2
    @54
    @38
    @1
    c3
    @7
    cle
    wbr
    #
    @54
    cn0
    wcel
    #
    @1
    c3
    c1
    cmin
    co
    #
    cN
    cle
    wbr
    @58
    @1
    @60
    c2
    cN
    cle
    3m1e2
    c2
    cN
    eluzle
    syl5eqbr
    @1
    c3
    c1
    cN
    c3
    cr
    wcel
    @1
    3re
    a1i
    @1
    1red
    c2
    cN
    eluzelre
    lesubaddd
    mpbid
    @1
    c3
    cn0
    wcel
    #
    @39
    @58
    @59
    wb
    3nn0
    @40
    c3
    @7
    nn0sub
    sylancr
    mpbid
    nnexpcld
    nnzd
    @50
    @55
    wceq
    #
    @52
    @57
    wb
    @1
    @62
    @51
    @56
    @8
    @50
    @55
    c8
    cmul
    oveq2
    eqeq1d
    adantl
    @1
    @56
    c2
    c3
    cexp
    co
    #
    @8
    @63
    cdiv
    co
    #
    cmul
    co
    @8
    @1
    c8
    @63
    @55
    @64
    cmul
    c8
    @63
    wceq
    @1
    @63
    c8
    cu2
    eqcomi
    a1i
    @1
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    wa
    #
    @7
    cz
    wcel
    c3
    cz
    wcel
    #
    @55
    @64
    wceq
    @67
    @1
    2cnne0
    a1i
    @1
    cN
    c2
    cN
    eluzelz
    peano2zd
    @68
    @1
    3z
    a1i
    c2
    @7
    c3
    expsub
    syl12anc
    oveq12d
    @1
    @8
    @63
    @41
    @63
    cc
    wcel
    @1
    @63
    @37
    @61
    @63
    cn
    wcel
    2nn
    3nn0
    c2
    c3
    nnexpcl
    mp2an
    nncni
    a1i
    @63
    cc0
    wne
    #
    @1
    @65
    @66
    @68
    @69
    2cn
    2ne0
    3z
    c2
    c3
    expne0i
    mp3an
    a1i
    divcan2d
    eqtrd
    rspcedvd
    @1
    c8
    cn
    wcel
    @8
    cz
    wcel
    @53
    @49
    wb
    8nn
    @1
    @8
    @1
    c2
    @7
    c2
    cn0
    wcel
    @1
    2nn0
    a1i
    @40
    nn0expcld
    nn0zd
    vk
    c8
    @8
    zdiv
    sylancr
    mpbid
    adantr
    @17
    @6
    cz
    wcel
    @1
    @6
    nnz
    adantl
    zmulcld
    @48
    @24
    c8
    cz
    wcel
    c2
    c8
    cle
    wbr
    2z
    c8
    8nn
    nnzi
    c2
    c8
    2re
    8re
    2lt8
    ltleii
    c2
    c8
    eluz2
    mpbir3an
    @31
    c8
    mulp1mod1
    sylancl
    c1
    cn
    wcel
    c1
    @27
    wcel
    @29
    1nn
    c1
    c7
    cn
    prid1g
    mp1i
    eqeltrd
    adantr
    eqeltrd
    ex
    sylbid
    3ad2antl1
    imp
    @5
    @25
    @28
    wb
    #
    @17
    @11
    @3
    @1
    @70
    @4
    @3
    @15
    @70
    @16
    cP
    2lgs
    syl
    3ad2ant2
    ad2antrr
    mpbird
    oveq1d
    @5
    @22
    c1
    wceq
    #
    @17
    @11
    @3
    @1
    @71
    @4
    @3
    @15
    cP
    cr
    wcel
    #
    c1
    cP
    clt
    wbr
    #
    wa
    #
    @71
    @16
    @15
    cP
    @0
    wcel
    #
    @74
    cP
    prmuz2
    @75
    @72
    @73
    c2
    cP
    eluzelre
    cP
    eluz2gt1
    jca
    syl
    cP
    1mod
    3syl
    3ad2ant2
    ad2antrr
    3eqtrd
    ex
    rexlimdva
    mpd
end
