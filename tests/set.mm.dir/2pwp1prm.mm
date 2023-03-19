include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cprime.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "cn0.mm"
include "wrex.mm"
include "wn.mm"
include "cdvds.mm"
include "wbr.mm"
include "csn.mm"
include "cdif.mm"
include "oddprmdvds.mm"
include "adantlr.mm"
include "wi.mm"
include "cmul.mm"
include "wb.mm"
include "eldifi.mm"
include "prmnn.mm"
include "syl.mm"
include "simpl.mm"
include "nndivides.mm"
include "syl2anr.mm"
include "cneg.mm"
include "cmin.mm"
include "clt.mm"
include "cle.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "nnnn0.mm"
include "1le2.mm"
include "expge1d.mm"
include "cz.mm"
include "1zzd.mm"
include "2nn.mm"
include "nnexpcld.mm"
include "nnzd.mm"
include "zleltp1.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "cc.mm"
include "nncnd.mm"
include "1cnd.mm"
include "subneg.mm"
include "breq2d.mm"
include "mpbird.mm"
include "adantl.mm"
include "ad2antlr.mm"
include "nnred.mm"
include "nnnn0d.mm"
include "adantr.mm"
include "nn0mulcld.mm"
include "1red.mm"
include "nnz.mm"
include "zmulcld.mm"
include "1lt2.mm"
include "prmgt1.mm"
include "cc0.mm"
include "nnre.mm"
include "nngt0.mm"
include "ltmulgt11.mm"
include "syl3anc.mm"
include "ltexp2a.mm"
include "syl32anc.mm"
include "ltadd1dd.mm"
include "subnegd.mm"
include "eqcomd.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "3brtr3d.mm"
include "cfzo.mm"
include "csu.mm"
include "neg1z.mm"
include "zsubcld.mm"
include "cfn.mm"
include "fzofi.mm"
include "elfzonn0.mm"
include "zexpcl.mm"
include "syl2an.mm"
include "fzonnsub.mm"
include "nnm1nn0.mm"
include "fsumzcl.mm"
include "dvdsmul1.mm"
include "neg1cn.mm"
include "pwdif.mm"
include "2cnd.mm"
include "expcld.mm"
include "eqcoms.mm"
include "expmuld.mm"
include "eqtrd.mm"
include "1exp.mm"
include "negeqd.mm"
include "oddn2prm.mm"
include "oexpneg.mm"
include "oveq12d.mm"
include "dvdsnprmd.mm"
include "pm2.21d.mm"
include "ex.mm"
include "com23.mm"
include "impancom.mm"
include "impl.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "mpd.mm"
include "pm2.18da.mm"

theorem 2pwp1prm
  let vn: setvar n
  let cK: class K
  let vm: setvar m
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x

  disjoint K n
  disjoint K m
  disjoint K p
  disjoint m n
  disjoint m p
  disjoint n p
  disjoint k m
  disjoint k p
  disjoint k x
  assert |- ( ( K e. NN /\ ( ( 2 ^ K ) + 1 ) e. Prime ) -> E. n e. NN0 K = ( 2 ^ n ) )

  proof
    cK
    cn
    wcel
    #
    c2
    cK
    cexp
    co
    #
    c1
    caddc
    co
    #
    cprime
    wcel
    #
    wa
    #
    cK
    c2
    vn
    cv
    cexp
    co
    wceq
    vn
    cn0
    wrex
    #
    @4
    @5
    wn
    #
    wa
    vp
    cv
    #
    cK
    cdvds
    wbr
    #
    vp
    cprime
    c2
    csn
    #
    cdif
    #
    wrex
    #
    @5
    @0
    @6
    @11
    @3
    vn
    cK
    vp
    oddprmdvds
    adantlr
    @4
    @11
    @5
    wi
    @6
    @4
    @8
    @5
    vp
    @10
    @4
    @7
    @10
    wcel
    #
    wa
    #
    @8
    vm
    cv
    #
    @7
    cmul
    co
    #
    cK
    wceq
    #
    vm
    cn
    wrex
    #
    @5
    @12
    @7
    cn
    wcel
    #
    @0
    @8
    @17
    wb
    @4
    @12
    @7
    cprime
    wcel
    #
    @18
    @7
    cprime
    @9
    eldifi
    #
    @7
    prmnn
    syl
    #
    @0
    @3
    simpl
    vm
    @7
    cK
    nndivides
    syl2anr
    @13
    @16
    @5
    vm
    cn
    @4
    @12
    @14
    cn
    wcel
    #
    @16
    @5
    wi
    #
    @0
    @12
    @22
    wa
    #
    @3
    @23
    @0
    @24
    wa
    #
    @16
    @3
    @5
    @25
    @16
    @3
    @5
    wi
    @25
    @16
    wa
    #
    @3
    @5
    @26
    c2
    @14
    cexp
    co
    #
    c1
    cneg
    #
    cmin
    co
    #
    @2
    @24
    c1
    @29
    clt
    wbr
    #
    @0
    @16
    @22
    @30
    @12
    @22
    @30
    c1
    @27
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @22
    c1
    @27
    cle
    wbr
    #
    @32
    @22
    c2
    @14
    c2
    cr
    wcel
    #
    @22
    2re
    a1i
    @14
    nnnn0
    #
    c1
    c2
    cle
    wbr
    @22
    1le2
    a1i
    expge1d
    @22
    c1
    cz
    wcel
    @27
    cz
    wcel
    #
    @33
    @32
    wb
    @22
    1zzd
    @22
    @27
    @22
    c2
    @14
    c2
    cn
    wcel
    #
    @22
    2nn
    a1i
    @35
    nnexpcld
    #
    nnzd
    #
    c1
    @27
    zleltp1
    syl2anc
    mpbid
    @22
    @27
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @30
    @32
    wb
    @22
    @27
    @38
    nncnd
    #
    @22
    1cnd
    #
    @40
    @41
    wa
    @29
    @31
    c1
    clt
    @27
    c1
    subneg
    breq2d
    syl2anc
    mpbird
    adantl
    ad2antlr
    @26
    @31
    c2
    @15
    cexp
    co
    #
    c1
    caddc
    co
    #
    @29
    @2
    clt
    @24
    @31
    @45
    clt
    wbr
    @0
    @16
    @24
    @27
    @44
    c1
    @22
    @27
    cr
    wcel
    @12
    @22
    @27
    @38
    nnred
    adantl
    @24
    @44
    @24
    c2
    @15
    @37
    @24
    2nn
    a1i
    @24
    @14
    @7
    @22
    @14
    cn0
    wcel
    @12
    @35
    adantl
    #
    @12
    @7
    cn0
    wcel
    #
    @22
    @12
    @7
    @21
    nnnn0d
    adantr
    #
    nn0mulcld
    nnexpcld
    nnred
    @24
    1red
    @24
    @34
    @14
    cz
    wcel
    #
    @15
    cz
    wcel
    c1
    c2
    clt
    wbr
    #
    @14
    @15
    clt
    wbr
    #
    @27
    @44
    clt
    wbr
    @34
    @24
    2re
    a1i
    @22
    @49
    @12
    @14
    nnz
    adantl
    #
    @24
    @14
    @7
    @52
    @12
    @7
    cz
    wcel
    #
    @22
    @12
    @7
    @21
    nnzd
    #
    adantr
    zmulcld
    @50
    @24
    1lt2
    a1i
    @24
    c1
    @7
    clt
    wbr
    #
    @51
    @12
    @55
    @22
    @12
    @19
    @55
    @20
    @7
    prmgt1
    syl
    adantr
    @24
    @14
    cr
    wcel
    #
    @7
    cr
    wcel
    #
    cc0
    @14
    clt
    wbr
    #
    @55
    @51
    wb
    @22
    @56
    @12
    @14
    nnre
    adantl
    @12
    @57
    @22
    @12
    @7
    @21
    nnred
    adantr
    @22
    @58
    @12
    @14
    nngt0
    adantl
    @14
    @7
    ltmulgt11
    syl3anc
    mpbid
    c2
    @14
    @15
    ltexp2a
    syl32anc
    ltadd1dd
    ad2antlr
    @24
    @31
    @29
    wceq
    #
    @0
    @16
    @22
    @59
    @12
    @22
    @29
    @31
    @22
    @27
    c1
    @42
    @43
    subnegd
    eqcomd
    adantl
    ad2antlr
    @16
    @45
    @2
    wceq
    @25
    @16
    @44
    @1
    c1
    caddc
    @15
    cK
    c2
    cexp
    oveq2
    oveq1d
    adantl
    3brtr3d
    @26
    @29
    @2
    cdvds
    wbr
    @29
    @27
    @7
    cexp
    co
    #
    @28
    @7
    cexp
    co
    #
    cmin
    co
    #
    cdvds
    wbr
    #
    @26
    @63
    @29
    @29
    cc0
    @7
    cfzo
    co
    #
    @27
    vk
    cv
    #
    cexp
    co
    #
    @28
    @7
    @65
    cmin
    co
    #
    c1
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmul
    co
    #
    cdvds
    wbr
    #
    @24
    @73
    @0
    @16
    @24
    @29
    cz
    wcel
    #
    @71
    cz
    wcel
    @73
    @22
    @74
    @12
    @22
    @27
    @28
    @39
    @28
    cz
    wcel
    #
    @22
    neg1z
    a1i
    zsubcld
    adantl
    @24
    @64
    @70
    vk
    @64
    cfn
    wcel
    @24
    cc0
    @7
    fzofi
    a1i
    @24
    @65
    @64
    wcel
    #
    wa
    #
    @66
    @69
    @24
    @36
    @65
    cn0
    wcel
    @66
    cz
    wcel
    @76
    @22
    @36
    @12
    @39
    adantl
    @65
    @7
    elfzonn0
    @27
    @65
    zexpcl
    syl2an
    @77
    @75
    @68
    cn0
    wcel
    #
    @69
    cz
    wcel
    @75
    @77
    neg1z
    a1i
    @77
    @67
    cn
    wcel
    #
    @78
    @76
    @79
    @24
    @65
    cc0
    @7
    fzonnsub
    adantl
    @67
    nnm1nn0
    syl
    @28
    @68
    zexpcl
    syl2anc
    zmulcld
    fsumzcl
    @29
    @71
    dvdsmul1
    syl2anc
    ad2antlr
    @24
    @63
    @73
    wb
    @0
    @16
    @24
    @62
    @72
    @29
    cdvds
    @24
    @47
    @40
    @28
    cc
    wcel
    #
    @62
    @72
    wceq
    @48
    @22
    @40
    @12
    @42
    adantl
    @80
    @24
    neg1cn
    a1i
    @27
    @28
    vk
    @7
    pwdif
    syl3anc
    breq2d
    ad2antlr
    mpbird
    @26
    @2
    @62
    @29
    cdvds
    @26
    @2
    @1
    @28
    cmin
    co
    #
    @62
    @25
    @2
    @81
    wceq
    #
    @16
    @0
    @82
    @24
    @0
    @81
    @2
    @0
    @1
    c1
    @0
    c2
    cK
    @0
    2cnd
    cK
    nnnn0
    expcld
    @0
    1cnd
    subnegd
    eqcomd
    adantr
    adantr
    @26
    @1
    @60
    @28
    @61
    cmin
    @26
    @1
    @44
    @60
    @16
    @1
    @44
    wceq
    #
    @25
    @83
    cK
    @15
    cK
    @15
    c2
    cexp
    oveq2
    eqcoms
    adantl
    @24
    @44
    @60
    wceq
    @0
    @16
    @24
    c2
    @14
    @7
    @24
    2cnd
    @48
    @46
    expmuld
    ad2antlr
    eqtrd
    @24
    @28
    @61
    wceq
    #
    @0
    @16
    @12
    @84
    @22
    @12
    @28
    c1
    @7
    cexp
    co
    #
    cneg
    #
    @61
    @12
    c1
    @85
    @12
    @85
    c1
    @12
    @53
    @85
    c1
    wceq
    @54
    @7
    1exp
    syl
    eqcomd
    negeqd
    @12
    @61
    @86
    @12
    @41
    @18
    c2
    @7
    cdvds
    wbr
    wn
    @61
    @86
    wceq
    @12
    1cnd
    @21
    @7
    oddn2prm
    c1
    @7
    oexpneg
    syl3anc
    eqcomd
    eqtrd
    adantr
    ad2antlr
    oveq12d
    eqtrd
    breq2d
    mpbird
    dvdsnprmd
    pm2.21d
    ex
    com23
    impancom
    impl
    rexlimdva
    sylbid
    rexlimdva
    adantr
    mpd
    pm2.18da
end
