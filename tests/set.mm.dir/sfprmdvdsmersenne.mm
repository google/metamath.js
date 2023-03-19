include "cprime.mm"
include "wcel.mm"
include "c8.mm"
include "cmo.mm"
include "co.mm"
include "c7.mm"
include "wceq.mm"
include "c2.mm"
include "cmul.mm"
include "c1.mm"
include "caddc.mm"
include "cexp.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "wi.mm"
include "wa.mm"
include "cpr.mm"
include "wo.mm"
include "olc.mm"
include "cvv.mm"
include "wb.mm"
include "ovex.mm"
include "elprg.mm"
include "mp1i.mm"
include "mpbird.mm"
include "clgs.mm"
include "2lgs.mm"
include "ad2antlr.mm"
include "cv.mm"
include "wn.mm"
include "cz.mm"
include "wrex.mm"
include "csn.mm"
include "cdif.mm"
include "2z.mm"
include "wne.mm"
include "simpr.mm"
include "adantr.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "clt.mm"
include "2m1e1.mm"
include "prmnn.mm"
include "nnred.mm"
include "1lt2.mm"
include "prmgt1.mm"
include "mulgt1d.mm"
include "syl5eqbr.mm"
include "1red.mm"
include "cn.mm"
include "2nn.mm"
include "nnmulcld.mm"
include "ltsubaddd.mm"
include "mpbid.mm"
include "ad2antrr.mm"
include "breq2.mm"
include "adantl.mm"
include "gtned.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "lgsqrmodndvds.mm"
include "sylancr.mm"
include "cdiv.mm"
include "cc.mm"
include "nncnd.mm"
include "1cnd.mm"
include "2cnd.mm"
include "mulcld.mm"
include "subadd2d.mm"
include "cc0.mm"
include "prmz.mm"
include "peano2zm.mm"
include "syl.mm"
include "zcnd.mm"
include "2cnne0.mm"
include "divmul2.mm"
include "syl3anc.mm"
include "eqcom.mm"
include "3bitr4rd.mm"
include "biimpa.mm"
include "oveq2.mm"
include "cn0.mm"
include "crp.mm"
include "zsqcl.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "pncan1.mm"
include "2ne0.mm"
include "divcan3d.mm"
include "eqtrd.mm"
include "nnnn0d.mm"
include "eqeltrd.mm"
include "nnrpd.mm"
include "jca.mm"
include "modexp.mm"
include "syl211anc.mm"
include "ex.mm"
include "divcan2d.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "ad3antlr.mm"
include "zcn.mm"
include "2nn0.mm"
include "expmuld.mm"
include "eqtr2d.mm"
include "vfermltl.mm"
include "ad5ant245.mm"
include "eqeqan12d.mm"
include "id.mm"
include "1mod.mm"
include "syl2anc.mm"
include "sylan9eqr.mm"
include "ad4antlr.mm"
include "zexpcl.mm"
include "ad4antr.mm"
include "1zzd.mm"
include "moddvds.mm"
include "sylbid.mm"
include "com23.mm"
include "syld.mm"
include "impd.mm"
include "syl5.mm"
include "mpd.mm"
include "rexlimdv.mm"
include "sylbird.mm"
include "3imp2.mm"

theorem sfprmdvdsmersenne
  let cP: class P
  let cQ: class Q
  let vm: setvar m
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( P e. Prime /\ ( Q e. Prime /\ ( Q mod 8 ) = 7 /\ Q = ( ( 2 x. P ) + 1 ) ) ) -> Q || ( ( 2 ^ P ) - 1 ) )

  proof
    cP
    cprime
    wcel
    #
    cQ
    cprime
    wcel
    #
    cQ
    c8
    cmo
    co
    #
    c7
    wceq
    #
    cQ
    c2
    cP
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    cQ
    c2
    cP
    cexp
    co
    #
    c1
    cmin
    co
    cdvds
    wbr
    #
    @0
    @1
    @3
    @6
    @8
    wi
    wi
    @0
    @1
    wa
    #
    @6
    @3
    @8
    @9
    @6
    @3
    @8
    wi
    @3
    @2
    c1
    c7
    cpr
    wcel
    #
    @9
    @6
    wa
    #
    @8
    @3
    @10
    @2
    c1
    wceq
    #
    @3
    wo
    #
    @3
    @12
    olc
    @2
    cvv
    wcel
    @10
    @13
    wb
    @3
    cQ
    c8
    cmo
    ovex
    @2
    c1
    c7
    cvv
    elprg
    mp1i
    mpbird
    @11
    @10
    c2
    cQ
    clgs
    co
    c1
    wceq
    #
    @8
    @1
    @14
    @10
    wb
    @0
    @6
    cQ
    2lgs
    ad2antlr
    @11
    @14
    vm
    cv
    #
    c2
    cexp
    co
    #
    cQ
    cmo
    co
    c2
    cQ
    cmo
    co
    wceq
    #
    cQ
    @15
    cdvds
    wbr
    wn
    #
    wa
    #
    vm
    cz
    wrex
    #
    @8
    @11
    c2
    cz
    wcel
    #
    cQ
    cprime
    c2
    csn
    cdif
    wcel
    #
    @14
    @20
    wi
    2z
    @11
    @1
    cQ
    c2
    wne
    @22
    @9
    @1
    @6
    @0
    @1
    simpr
    adantr
    @11
    c2
    cQ
    c2
    cr
    wcel
    #
    @11
    2re
    a1i
    @11
    c2
    cQ
    clt
    wbr
    #
    c2
    @5
    clt
    wbr
    #
    @0
    @25
    @1
    @6
    @0
    c2
    c1
    cmin
    co
    #
    @4
    clt
    wbr
    @25
    @0
    @26
    c1
    @4
    clt
    2m1e1
    @0
    c2
    cP
    @23
    @0
    2re
    a1i
    #
    @0
    cP
    cP
    prmnn
    #
    nnred
    c1
    c2
    clt
    wbr
    @0
    1lt2
    a1i
    cP
    prmgt1
    mulgt1d
    syl5eqbr
    @0
    c2
    c1
    @4
    @27
    @0
    1red
    @0
    @4
    @0
    c2
    cP
    c2
    cn
    wcel
    @0
    2nn
    a1i
    @28
    nnmulcld
    nnred
    ltsubaddd
    mpbid
    ad2antrr
    @6
    @24
    @25
    wb
    @9
    cQ
    @5
    c2
    clt
    breq2
    adantl
    mpbird
    gtned
    cQ
    cprime
    c2
    eldifsn
    sylanbrc
    vm
    c2
    cQ
    lgsqrmodndvds
    sylancr
    @11
    @19
    @8
    vm
    cz
    @11
    cQ
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cP
    wceq
    #
    @15
    cz
    wcel
    #
    @19
    @8
    wi
    #
    wi
    #
    @9
    @6
    @31
    @9
    @29
    @4
    wceq
    #
    @5
    cQ
    wceq
    #
    @31
    @6
    @9
    cQ
    c1
    @4
    @1
    cQ
    cc
    wcel
    @0
    @1
    cQ
    cQ
    prmnn
    #
    nncnd
    adantl
    @9
    1cnd
    @0
    @4
    cc
    wcel
    #
    @1
    @0
    c2
    cP
    @0
    2cnd
    #
    @0
    cP
    @28
    nncnd
    #
    mulcld
    #
    adantr
    subadd2d
    @9
    @29
    cc
    wcel
    #
    cP
    cc
    wcel
    #
    c2
    cc
    wcel
    c2
    cc0
    wne
    #
    wa
    #
    @31
    @35
    wb
    @1
    @42
    @0
    @1
    @29
    @1
    cQ
    cz
    wcel
    @29
    cz
    wcel
    cQ
    prmz
    cQ
    peano2zm
    syl
    zcnd
    #
    adantl
    @0
    @43
    @1
    @40
    adantr
    @45
    @9
    2cnne0
    a1i
    @29
    cP
    c2
    divmul2
    syl3anc
    @6
    @36
    wb
    @9
    cQ
    @5
    eqcom
    a1i
    3bitr4rd
    biimpa
    @31
    c2
    @30
    cexp
    co
    #
    @7
    wceq
    #
    @11
    @34
    @30
    cP
    c2
    cexp
    oveq2
    @11
    @32
    @48
    @33
    @11
    @32
    @48
    @33
    wi
    @11
    @32
    wa
    #
    @19
    @48
    @8
    @49
    @17
    @18
    @48
    @8
    wi
    #
    @49
    @18
    @17
    @50
    @49
    @18
    @17
    @50
    wi
    @49
    @18
    wa
    #
    @17
    @16
    @30
    cexp
    co
    #
    cQ
    cmo
    co
    #
    @47
    cQ
    cmo
    co
    #
    wceq
    #
    @50
    @49
    @17
    @55
    wi
    @18
    @49
    @17
    @55
    @49
    @17
    wa
    #
    @16
    cz
    wcel
    #
    @21
    @30
    cn0
    wcel
    #
    cQ
    crp
    wcel
    #
    wa
    #
    @17
    @55
    @32
    @57
    @11
    @17
    @15
    zsqcl
    ad2antlr
    @21
    @56
    2z
    a1i
    @11
    @60
    @32
    @17
    @11
    @58
    @59
    @11
    @30
    cP
    cn0
    @11
    @30
    @5
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cP
    @11
    @29
    @61
    c2
    cdiv
    @6
    @29
    @61
    wceq
    @9
    cQ
    @5
    c1
    cmin
    oveq1
    adantl
    oveq1d
    @0
    @62
    cP
    wceq
    @1
    @6
    @0
    @62
    @4
    c2
    cdiv
    co
    cP
    @0
    @61
    @4
    c2
    cdiv
    @0
    @38
    @61
    @4
    wceq
    @41
    @4
    pncan1
    syl
    oveq1d
    @0
    cP
    c2
    @40
    @39
    @44
    @0
    2ne0
    a1i
    divcan3d
    eqtrd
    ad2antrr
    eqtrd
    @0
    cP
    cn0
    wcel
    #
    @1
    @6
    @0
    cP
    @28
    nnnn0d
    #
    ad2antrr
    eqeltrd
    #
    @1
    @59
    @0
    @6
    @1
    cQ
    @37
    nnrpd
    ad2antlr
    jca
    ad2antrr
    @49
    @17
    simpr
    @16
    c2
    @30
    cQ
    modexp
    syl211anc
    ex
    adantr
    @51
    @48
    @55
    @8
    @51
    @48
    @55
    @8
    wi
    @51
    @48
    wa
    @55
    c1
    @7
    cQ
    cmo
    co
    #
    wceq
    #
    @8
    @51
    @48
    @53
    c1
    @54
    @66
    @51
    @53
    @15
    @29
    cexp
    co
    #
    cQ
    cmo
    co
    #
    c1
    @49
    @53
    @69
    wceq
    @18
    @49
    @52
    @68
    cQ
    cmo
    @49
    @68
    @15
    c2
    @30
    cmul
    co
    #
    cexp
    co
    #
    @52
    @1
    @68
    @71
    wceq
    @0
    @6
    @32
    @1
    @29
    @70
    @15
    cexp
    @1
    @70
    @29
    @1
    @29
    c2
    @46
    @1
    2cnd
    @44
    @1
    2ne0
    a1i
    divcan2d
    eqcomd
    oveq2d
    ad3antlr
    @49
    @15
    c2
    @30
    @32
    @15
    cc
    wcel
    @11
    @15
    zcn
    adantl
    @11
    @58
    @32
    @65
    adantr
    c2
    cn0
    wcel
    @49
    2nn0
    a1i
    expmuld
    eqtr2d
    oveq1d
    adantr
    @1
    @32
    @18
    @69
    c1
    wceq
    @0
    @6
    @15
    cQ
    vfermltl
    ad5ant245
    eqtrd
    @47
    @7
    cQ
    cmo
    oveq1
    eqeqan12d
    @49
    @67
    @8
    wi
    @18
    @48
    @49
    @67
    @8
    @49
    @67
    wa
    #
    @66
    c1
    cQ
    cmo
    co
    #
    wceq
    #
    @8
    @67
    @49
    @66
    c1
    @73
    @67
    c1
    @66
    @67
    id
    eqcomd
    @1
    c1
    @73
    wceq
    @0
    @6
    @32
    @1
    @73
    c1
    @1
    cQ
    cr
    wcel
    c1
    cQ
    clt
    wbr
    @73
    c1
    wceq
    @1
    cQ
    @37
    nnred
    cQ
    prmgt1
    cQ
    1mod
    syl2anc
    eqcomd
    ad3antlr
    sylan9eqr
    @72
    cQ
    cn
    wcel
    #
    @7
    cz
    wcel
    #
    c1
    cz
    wcel
    @74
    @8
    wb
    @1
    @75
    @0
    @6
    @32
    @67
    @37
    ad4antlr
    @0
    @76
    @1
    @6
    @32
    @67
    @0
    @21
    @63
    @76
    2z
    @64
    c2
    cP
    zexpcl
    sylancr
    ad4antr
    @72
    1zzd
    @7
    c1
    cQ
    moddvds
    syl3anc
    mpbid
    ex
    ad2antrr
    sylbid
    ex
    com23
    syld
    ex
    com23
    impd
    com23
    ex
    com23
    syl5
    mpd
    rexlimdv
    syld
    sylbird
    syl5
    ex
    com23
    ex
    3imp2
end
