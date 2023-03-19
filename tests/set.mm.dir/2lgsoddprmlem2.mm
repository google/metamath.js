include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "c8.mm"
include "cmo.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "wrex.mm"
include "cexp.mm"
include "c1.mm"
include "cmin.mm"
include "cdiv.mm"
include "wb.mm"
include "crp.mm"
include "wi.mm"
include "cn.mm"
include "8nn.mm"
include "nnrp.mm"
include "ax-mp.mm"
include "wa.mm"
include "eqcom.mm"
include "modmuladdim.mm"
include "syl5bi.mm"
include "mpan2.mm"
include "imp.mm"
include "3adant2.mm"
include "zcn.mm"
include "cc.mm"
include "8cn.mm"
include "a1i.mm"
include "mulcomd.mm"
include "adantl.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "simpr.mm"
include "adantr.mm"
include "id.mm"
include "zmodcld.mm"
include "nn0zd.mm"
include "3ad2ant1.mm"
include "eleq1.mm"
include "3ad2ant3.mm"
include "mpbird.mm"
include "2lgsoddprmlem1.mm"
include "syl3anc.mm"
include "breq2d.mm"
include "cr.mm"
include "2z.mm"
include "simp1.mm"
include "nn0red.mm"
include "resqcl.mm"
include "peano2rem.mm"
include "syl.mm"
include "8re.mm"
include "cc0.mm"
include "wne.mm"
include "8pos.mm"
include "gt0ne0ii.mm"
include "redivcld.mm"
include "cn0.mm"
include "nn0z.mm"
include "nnzi.mm"
include "zsqcl.mm"
include "zmulcld.mm"
include "zmulcl.mm"
include "ancoms.mm"
include "zaddcld.mm"
include "c4.mm"
include "4z.mm"
include "jca.mm"
include "dvdsmul1.mm"
include "4t2e8.mm"
include "4cn.mm"
include "2cn.mm"
include "mulcomi.mm"
include "eqtr3i.mm"
include "zcnd.mm"
include "mulassd.mm"
include "eqtrd.mm"
include "adddid.mm"
include "eqtr4d.mm"
include "breqtrrd.mm"
include "ex.mm"
include "dvdsaddre2b.mm"
include "mp3an2ani.mm"
include "bitr4d.mm"
include "sylbid.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem 2lgsoddprmlem2
  let cR: class R
  let cN: class N
  let vk: setvar k


  assert |- ( ( N e. ZZ /\ -. 2 || N /\ R = ( N mod 8 ) ) -> ( 2 || ( ( ( N ^ 2 ) - 1 ) / 8 ) <-> 2 || ( ( ( R ^ 2 ) - 1 ) / 8 ) ) )

  proof
    cN
    cz
    wcel
    #
    c2
    cN
    cdvds
    wbr
    wn
    #
    cR
    cN
    c8
    cmo
    co
    #
    wceq
    #
    w3a
    #
    cN
    vk
    cv
    #
    c8
    cmul
    co
    #
    cR
    caddc
    co
    #
    wceq
    #
    vk
    cz
    wrex
    #
    c2
    cN
    c2
    cexp
    co
    c1
    cmin
    co
    c8
    cdiv
    co
    #
    cdvds
    wbr
    #
    c2
    cR
    c2
    cexp
    co
    #
    c1
    cmin
    co
    #
    c8
    cdiv
    co
    #
    cdvds
    wbr
    #
    wb
    #
    @0
    @3
    @9
    @1
    @0
    @3
    @9
    @0
    c8
    crp
    wcel
    #
    @3
    @9
    wi
    c8
    cn
    wcel
    #
    @17
    8nn
    c8
    nnrp
    ax-mp
    @3
    @2
    cR
    wceq
    @0
    @17
    wa
    @9
    cR
    @2
    eqcom
    cN
    cR
    vk
    c8
    modmuladdim
    syl5bi
    mpan2
    imp
    3adant2
    @4
    @8
    @16
    vk
    cz
    @4
    @5
    cz
    wcel
    #
    wa
    #
    @8
    cN
    c8
    @5
    cmul
    co
    #
    cR
    caddc
    co
    #
    wceq
    #
    @16
    @20
    @7
    @22
    cN
    @20
    @6
    @21
    cR
    caddc
    @19
    @6
    @21
    wceq
    @4
    @19
    @5
    c8
    @5
    zcn
    c8
    cc
    wcel
    @19
    8cn
    a1i
    mulcomd
    adantl
    oveq1d
    eqeq2d
    @20
    @23
    @16
    @20
    @23
    wa
    #
    @11
    c2
    c8
    @5
    c2
    cexp
    co
    #
    cmul
    co
    #
    c2
    @5
    cR
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @14
    caddc
    co
    #
    cdvds
    wbr
    #
    @15
    @24
    @10
    @30
    c2
    cdvds
    @24
    @19
    cR
    cz
    wcel
    #
    @23
    @10
    @30
    wceq
    @20
    @19
    @23
    @4
    @19
    simpr
    adantr
    @20
    @32
    @23
    @4
    @32
    @19
    @4
    @32
    @2
    cz
    wcel
    #
    @0
    @1
    @33
    @3
    @0
    @2
    @0
    cN
    c8
    @0
    id
    @18
    @0
    8nn
    a1i
    zmodcld
    nn0zd
    3ad2ant1
    @3
    @0
    @32
    @33
    wb
    @1
    cR
    @2
    cz
    eleq1
    3ad2ant3
    mpbird
    adantr
    adantr
    @20
    @23
    simpr
    @5
    cR
    cN
    2lgsoddprmlem1
    syl3anc
    breq2d
    c2
    cz
    wcel
    #
    @20
    @14
    cr
    wcel
    #
    @23
    @29
    cz
    wcel
    #
    c2
    @29
    cdvds
    wbr
    #
    wa
    #
    @15
    @31
    wb
    2z
    @4
    @35
    @19
    @4
    cR
    cr
    wcel
    #
    @35
    @4
    @39
    @2
    cr
    wcel
    #
    @4
    @2
    @4
    cN
    c8
    @0
    @1
    @3
    simp1
    @18
    @4
    8nn
    a1i
    zmodcld
    #
    nn0red
    @3
    @0
    @39
    @40
    wb
    @1
    cR
    @2
    cr
    eleq1
    3ad2ant3
    mpbird
    @39
    @13
    c8
    @39
    @12
    cr
    wcel
    @13
    cr
    wcel
    cR
    resqcl
    @12
    peano2rem
    syl
    c8
    cr
    wcel
    @39
    8re
    a1i
    c8
    cc0
    wne
    @39
    c8
    8re
    8pos
    gt0ne0ii
    a1i
    redivcld
    syl
    adantr
    @20
    @38
    @23
    @4
    @19
    @38
    @4
    cR
    cn0
    wcel
    #
    @19
    @38
    wi
    #
    @4
    @42
    @2
    cn0
    wcel
    #
    @41
    @3
    @0
    @42
    @44
    wb
    @1
    cR
    @2
    cn0
    eleq1
    3ad2ant3
    mpbird
    @42
    @32
    @43
    cR
    nn0z
    @32
    @19
    @38
    @32
    @19
    wa
    #
    @36
    @37
    @45
    @26
    @28
    @45
    c8
    @25
    c8
    cz
    wcel
    @45
    c8
    8nn
    nnzi
    a1i
    @19
    @25
    cz
    wcel
    @32
    @5
    zsqcl
    #
    adantl
    #
    zmulcld
    @45
    c2
    @27
    @34
    @45
    2z
    a1i
    #
    @19
    @32
    @27
    cz
    wcel
    @5
    cR
    zmulcl
    #
    ancoms
    #
    zmulcld
    zaddcld
    @45
    c2
    c2
    c4
    @25
    cmul
    co
    #
    @27
    caddc
    co
    #
    cmul
    co
    #
    @29
    cdvds
    @45
    @34
    @52
    cz
    wcel
    #
    wa
    c2
    @53
    cdvds
    wbr
    @45
    @34
    @54
    @48
    @45
    @51
    @27
    @45
    c4
    @25
    c4
    cz
    wcel
    @45
    4z
    a1i
    @47
    zmulcld
    #
    @50
    zaddcld
    jca
    c2
    @52
    dvdsmul1
    syl
    @45
    @29
    c2
    @51
    cmul
    co
    #
    @28
    caddc
    co
    @53
    @45
    @26
    @56
    @28
    caddc
    @45
    @26
    c2
    c4
    cmul
    co
    #
    @25
    cmul
    co
    @56
    @45
    c8
    @57
    @25
    cmul
    c8
    @57
    wceq
    @45
    c4
    c2
    cmul
    co
    c8
    @57
    4t2e8
    c4
    c2
    4cn
    2cn
    mulcomi
    eqtr3i
    a1i
    oveq1d
    @45
    c2
    c4
    @25
    c2
    cc
    wcel
    @45
    2cn
    a1i
    #
    c4
    cc
    wcel
    @45
    4cn
    a1i
    @19
    @25
    cc
    wcel
    @32
    @19
    @25
    @46
    zcnd
    adantl
    mulassd
    eqtrd
    oveq1d
    @45
    c2
    @51
    @27
    @58
    @45
    @51
    @55
    zcnd
    @19
    @32
    @27
    cc
    wcel
    @19
    @32
    wa
    @27
    @49
    zcnd
    ancoms
    adddid
    eqtr4d
    breqtrrd
    jca
    ex
    syl
    syl
    imp
    adantr
    c2
    @14
    @29
    dvdsaddre2b
    mp3an2ani
    bitr4d
    ex
    sylbid
    rexlimdva
    mpd
end
