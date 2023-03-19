include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "cneg.mm"
include "clgs.mm"
include "co.mm"
include "wceq.mm"
include "c4.mm"
include "cmo.mm"
include "cmin.mm"
include "cdiv.mm"
include "cexp.mm"
include "caddc.mm"
include "cdvds.mm"
include "wbr.mm"
include "cz.mm"
include "cn0.mm"
include "neg1z.mm"
include "oddprm.mm"
include "nnnn0d.mm"
include "zexpcl.mm"
include "sylancr.mm"
include "peano2zd.mm"
include "cn.mm"
include "eldifi.mm"
include "prmnn.mm"
include "syl.mm"
include "zmodcld.mm"
include "nn0cnd.mm"
include "1cnd.mm"
include "subaddd.mm"
include "cr.mm"
include "crp.mm"
include "cc0.mm"
include "cle.mm"
include "clt.mm"
include "2re.mm"
include "a1i.mm"
include "nnrpd.mm"
include "0le2.mm"
include "wne.mm"
include "eldifsni.mm"
include "nnred.mm"
include "cuz.mm"
include "cfv.mm"
include "prmuz2.mm"
include "eluzle.mm"
include "leltned.mm"
include "mpbird.mm"
include "modid.mm"
include "syl22anc.mm"
include "df-2.mm"
include "syl6eq.mm"
include "eqeq1d.mm"
include "wn.mm"
include "wa.mm"
include "neneqd.mm"
include "wb.mm"
include "2prm.mm"
include "dvdsprm.mm"
include "sylancl.mm"
include "mtbird.mm"
include "adantr.mm"
include "cc.mm"
include "simpr.mm"
include "oexpneg.mm"
include "syl3anc.mm"
include "nnzd.mm"
include "1exp.mm"
include "negeqd.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "ax-1cn.mm"
include "neg1cn.mm"
include "1pneg1e0.mm"
include "addcomli.mm"
include "oveq2d.mm"
include "2cn.mm"
include "subid1i.mm"
include "breq2d.mm"
include "ex.mm"
include "con4d.mm"
include "2z.mm"
include "moddvds.mm"
include "4z.mm"
include "4ne0.mm"
include "nnm1nn0.mm"
include "nn0zd.mm"
include "dvdsval2.mm"
include "cmul.mm"
include "2ne0.mm"
include "divdiv1d.mm"
include "2t2e4.mm"
include "oveq2i.mm"
include "eleq1d.mm"
include "bitr4d.mm"
include "3imtr4d.mm"
include "neg1ne0.mm"
include "biimpa.mm"
include "expmulz.mm"
include "nncnd.mm"
include "divcan2d.mm"
include "neg1sqe1.mm"
include "oveq1i.mm"
include "syl5eq.mm"
include "3eqtr3d.mm"
include "syl6reqr.mm"
include "impbid.mm"
include "3bitr2d.mm"
include "lgsval3.mm"
include "mpan.mm"
include "4nn.mm"
include "prmz.mm"
include "1zzd.mm"
include "3bitr4d.mm"
include "1re.mm"
include "nnrp.mm"
include "ax-mp.mm"
include "0le1.mm"
include "1lt4.mm"
include "mp4an.mm"
include "eqeq2i.mm"
include "syl6bb.mm"

theorem m1lgs
  let cP: class P


  assert |- ( P e. ( Prime \ { 2 } ) -> ( ( -u 1 /L P ) = 1 <-> ( P mod 4 ) = 1 ) )

  proof
    cP
    cprime
    c2
    csn
    #
    cdif
    wcel
    #
    c1
    cneg
    #
    cP
    clgs
    co
    #
    c1
    wceq
    #
    cP
    c4
    cmo
    co
    #
    c1
    c4
    cmo
    co
    #
    wceq
    #
    @5
    c1
    wceq
    @1
    @2
    cP
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cexp
    co
    #
    c1
    caddc
    co
    #
    cP
    cmo
    co
    #
    c1
    cmin
    co
    #
    c1
    wceq
    #
    c4
    @8
    cdvds
    wbr
    #
    @4
    @7
    @1
    @14
    c1
    c1
    caddc
    co
    #
    @12
    wceq
    c2
    cP
    cmo
    co
    #
    @12
    wceq
    #
    @15
    @1
    @12
    c1
    c1
    @1
    @12
    @1
    @11
    cP
    @1
    @10
    @1
    @2
    cz
    wcel
    #
    @9
    cn0
    wcel
    @10
    cz
    wcel
    neg1z
    @1
    @9
    cP
    oddprm
    #
    nnnn0d
    @2
    @9
    zexpcl
    sylancr
    peano2zd
    #
    @1
    cP
    cprime
    wcel
    #
    cP
    cn
    wcel
    #
    cP
    cprime
    @0
    eldifi
    #
    cP
    prmnn
    syl
    #
    zmodcld
    nn0cnd
    @1
    1cnd
    #
    @26
    subaddd
    @1
    @17
    @16
    @12
    @1
    @17
    c2
    @16
    @1
    c2
    cr
    wcel
    #
    cP
    crp
    wcel
    cc0
    c2
    cle
    wbr
    #
    c2
    cP
    clt
    wbr
    #
    @17
    c2
    wceq
    @27
    @1
    2re
    a1i
    #
    @1
    cP
    @25
    nnrpd
    @28
    @1
    0le2
    a1i
    @1
    @29
    cP
    c2
    wne
    cP
    cprime
    c2
    eldifsni
    #
    @1
    c2
    cP
    @30
    @1
    cP
    @25
    nnred
    @1
    cP
    c2
    cuz
    cfv
    wcel
    #
    c2
    cP
    cle
    wbr
    @1
    @22
    @32
    @24
    cP
    prmuz2
    syl
    #
    c2
    cP
    eluzle
    syl
    leltned
    mpbird
    c2
    cP
    modid
    syl22anc
    df-2
    syl6eq
    eqeq1d
    @1
    @18
    @15
    @1
    cP
    c2
    @11
    cmin
    co
    #
    cdvds
    wbr
    #
    c2
    @9
    cdvds
    wbr
    #
    @18
    @15
    @1
    @36
    @35
    @1
    @36
    wn
    #
    @35
    wn
    @1
    @37
    wa
    #
    @35
    cP
    c2
    cdvds
    wbr
    #
    @1
    @39
    wn
    @37
    @1
    @39
    cP
    c2
    wceq
    #
    @1
    cP
    c2
    @31
    neneqd
    @1
    @32
    c2
    cprime
    wcel
    @39
    @40
    wb
    @33
    2prm
    c2
    cP
    dvdsprm
    sylancl
    mtbird
    adantr
    @38
    @34
    c2
    cP
    cdvds
    @38
    @34
    c2
    cc0
    cmin
    co
    c2
    @38
    @11
    cc0
    c2
    cmin
    @38
    @11
    @2
    c1
    caddc
    co
    cc0
    @38
    @10
    @2
    c1
    caddc
    @38
    @10
    c1
    @9
    cexp
    co
    #
    cneg
    #
    @2
    @38
    c1
    cc
    wcel
    @9
    cn
    wcel
    #
    @37
    @10
    @42
    wceq
    @38
    1cnd
    @1
    @43
    @37
    @20
    adantr
    #
    @1
    @37
    simpr
    c1
    @9
    oexpneg
    syl3anc
    @38
    @41
    c1
    @38
    @9
    cz
    wcel
    #
    @41
    c1
    wceq
    @38
    @9
    @44
    nnzd
    @9
    1exp
    syl
    negeqd
    eqtrd
    oveq1d
    c1
    @2
    cc0
    ax-1cn
    neg1cn
    1pneg1e0
    addcomli
    syl6eq
    oveq2d
    c2
    2cn
    subid1i
    syl6eq
    breq2d
    mtbird
    ex
    con4d
    @1
    @23
    c2
    cz
    wcel
    #
    @11
    cz
    wcel
    @18
    @35
    wb
    @25
    @46
    @1
    2z
    a1i
    #
    @21
    c2
    @11
    cP
    moddvds
    syl3anc
    @1
    @15
    @9
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    @36
    @1
    @15
    @8
    c4
    cdiv
    co
    #
    cz
    wcel
    #
    @49
    @1
    c4
    cz
    wcel
    #
    c4
    cc0
    wne
    #
    @8
    cz
    wcel
    @15
    @51
    wb
    @52
    @1
    4z
    a1i
    @53
    @1
    4ne0
    a1i
    @1
    @8
    @1
    @23
    @8
    cn0
    wcel
    @25
    cP
    nnm1nn0
    syl
    #
    nn0zd
    c4
    @8
    dvdsval2
    syl3anc
    @1
    @48
    @50
    cz
    @1
    @48
    @8
    c2
    c2
    cmul
    co
    #
    cdiv
    co
    @50
    @1
    @8
    c2
    c2
    @1
    @8
    @54
    nn0cnd
    c2
    cc
    wcel
    @1
    2cn
    a1i
    #
    @56
    c2
    cc0
    wne
    #
    @1
    2ne0
    a1i
    #
    @58
    divdiv1d
    @55
    c4
    @8
    cdiv
    2t2e4
    oveq2i
    syl6eq
    eleq1d
    bitr4d
    #
    @1
    @46
    @57
    @45
    @36
    @49
    wb
    @47
    @58
    @1
    @9
    @20
    nnzd
    c2
    @9
    dvdsval2
    syl3anc
    bitr4d
    3imtr4d
    @1
    @15
    @18
    @1
    @15
    wa
    #
    c2
    @11
    cP
    cmo
    @60
    @11
    @16
    c2
    @60
    @10
    c1
    c1
    caddc
    @60
    @2
    c2
    @48
    cmul
    co
    #
    cexp
    co
    #
    @2
    c2
    cexp
    co
    #
    @48
    cexp
    co
    #
    @10
    c1
    @60
    @2
    cc
    wcel
    #
    @2
    cc0
    wne
    #
    @46
    @49
    @62
    @64
    wceq
    @65
    @60
    neg1cn
    a1i
    @66
    @60
    neg1ne0
    a1i
    @46
    @60
    2z
    a1i
    @1
    @15
    @49
    @59
    biimpa
    #
    @2
    c2
    @48
    expmulz
    syl22anc
    @60
    @61
    @9
    @2
    cexp
    @1
    @61
    @9
    wceq
    @15
    @1
    @9
    c2
    @1
    @9
    @20
    nncnd
    @56
    @58
    divcan2d
    adantr
    oveq2d
    @60
    @64
    c1
    @48
    cexp
    co
    #
    c1
    @63
    c1
    @48
    cexp
    neg1sqe1
    oveq1i
    @60
    @49
    @68
    c1
    wceq
    @67
    @48
    1exp
    syl
    syl5eq
    3eqtr3d
    oveq1d
    df-2
    syl6reqr
    oveq1d
    ex
    impbid
    3bitr2d
    @1
    @3
    @13
    c1
    @19
    @1
    @3
    @13
    wceq
    neg1z
    @2
    cP
    lgsval3
    mpan
    eqeq1d
    @1
    c4
    cn
    wcel
    #
    cP
    cz
    wcel
    #
    c1
    cz
    wcel
    @7
    @15
    wb
    @69
    @1
    4nn
    a1i
    @1
    @22
    @70
    @24
    cP
    prmz
    syl
    @1
    1zzd
    cP
    c1
    c4
    moddvds
    syl3anc
    3bitr4d
    @6
    c1
    @5
    c1
    cr
    wcel
    c4
    crp
    wcel
    #
    cc0
    c1
    cle
    wbr
    c1
    c4
    clt
    wbr
    @6
    c1
    wceq
    1re
    @69
    @71
    4nn
    c4
    nnrp
    ax-mp
    0le1
    1lt4
    c1
    c4
    modid
    mp4an
    eqeq2i
    syl6bb
end
