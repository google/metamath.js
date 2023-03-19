include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "clgs.mm"
include "cneg.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmul.mm"
include "cexp.mm"
include "cabs.mm"
include "cfv.mm"
include "cr.mm"
include "cz.mm"
include "simplrl.mm"
include "nnz.mm"
include "syl.mm"
include "ad3antrrr.mm"
include "lgscl.mm"
include "syl2anc.mm"
include "zred.mm"
include "absresq.mm"
include "gcdcom.mm"
include "simpr.mm"
include "eqtrd.mm"
include "wb.mm"
include "lgsabs1.mm"
include "mpbird.mm"
include "oveq1d.mm"
include "sq1.mm"
include "syl6eq.mm"
include "zcnd.mm"
include "sqvald.mm"
include "3eqtr3d.mm"
include "oveq2d.mm"
include "mulassd.mm"
include "eqtr4d.mm"
include "mulid1d.mm"
include "simplll.mm"
include "simpllr.mm"
include "simplrr.mm"
include "lgsquad2.mm"
include "cc0.mm"
include "cc.mm"
include "neg1cn.mm"
include "a1i.mm"
include "wne.mm"
include "neg1ne0.mm"
include "1zzd.mm"
include "cprime.mm"
include "2prm.mm"
include "nprmdvds1.mm"
include "mp1i.mm"
include "omoe.mm"
include "syl22anc.mm"
include "2z.mm"
include "2ne0.mm"
include "peano2zm.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "adantr.mm"
include "ad2antlr.mm"
include "zmulcld.mm"
include "expclzd.mm"
include "mul01d.mm"
include "lgsne0.mm"
include "eqeq1d.mm"
include "bitrd.mm"
include "syl2anr.mm"
include "necon1bbid.mm"
include "ad2ant2r.mm"
include "biimpa.mm"
include "syl2an.mm"
include "3eqtr4rd.mm"
include "pm2.61dan.mm"

theorem lgsquad3
  let cM: class M
  let cN: class N


  assert |- ( ( ( M e. NN /\ -. 2 || M ) /\ ( N e. NN /\ -. 2 || N ) ) -> ( M /L N ) = ( ( -u 1 ^ ( ( ( M - 1 ) / 2 ) x. ( ( N - 1 ) / 2 ) ) ) x. ( N /L M ) ) )

  proof
    cM
    cn
    wcel
    #
    c2
    cM
    cdvds
    wbr
    wn
    #
    wa
    #
    cN
    cn
    wcel
    #
    c2
    cN
    cdvds
    wbr
    wn
    #
    wa
    #
    wa
    #
    cM
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    cM
    cN
    clgs
    co
    #
    c1
    cneg
    #
    cM
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cN
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cmul
    co
    #
    cexp
    co
    #
    cN
    cM
    clgs
    co
    #
    cmul
    co
    #
    wceq
    @6
    @8
    wa
    #
    @9
    c1
    cmul
    co
    #
    @9
    @17
    cmul
    co
    #
    @17
    cmul
    co
    #
    @9
    @18
    @19
    @20
    @9
    @17
    @17
    cmul
    co
    #
    cmul
    co
    @22
    @19
    c1
    @23
    @9
    cmul
    @19
    @17
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    @17
    c2
    cexp
    co
    #
    c1
    @23
    @19
    @17
    cr
    wcel
    @25
    @26
    wceq
    @19
    @17
    @19
    cN
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    @17
    cz
    wcel
    @19
    @3
    @27
    @2
    @3
    @4
    @8
    simplrl
    #
    cN
    nnz
    #
    syl
    #
    @0
    @28
    @1
    @5
    @8
    cM
    nnz
    #
    ad3antrrr
    #
    cN
    cM
    lgscl
    syl2anc
    #
    zred
    @17
    absresq
    syl
    @19
    @25
    c1
    c2
    cexp
    co
    c1
    @19
    @24
    c1
    c2
    cexp
    @19
    @24
    c1
    wceq
    #
    cN
    cM
    cgcd
    co
    #
    c1
    wceq
    #
    @19
    @36
    @7
    c1
    @19
    @27
    @28
    @36
    @7
    wceq
    @31
    @33
    cN
    cM
    gcdcom
    #
    syl2anc
    @6
    @8
    simpr
    #
    eqtrd
    @19
    @27
    @28
    @35
    @37
    wb
    @31
    @33
    cN
    cM
    lgsabs1
    syl2anc
    mpbird
    oveq1d
    sq1
    syl6eq
    @19
    @17
    @19
    @17
    @34
    zcnd
    #
    sqvald
    3eqtr3d
    oveq2d
    @19
    @9
    @17
    @17
    @19
    @9
    @19
    @28
    @27
    @9
    cz
    wcel
    @33
    @31
    cM
    cN
    lgscl
    syl2anc
    zcnd
    #
    @40
    @40
    mulassd
    eqtr4d
    @19
    @9
    @41
    mulid1d
    @19
    @21
    @16
    @17
    cmul
    @19
    cM
    cN
    @0
    @1
    @5
    @8
    simplll
    @0
    @1
    @5
    @8
    simpllr
    @29
    @2
    @3
    @4
    @8
    simplrr
    @39
    lgsquad2
    oveq1d
    3eqtr3d
    @6
    @8
    wn
    #
    wa
    #
    @16
    cc0
    cmul
    co
    cc0
    @18
    @9
    @43
    @16
    @43
    @10
    @15
    @10
    cc
    wcel
    @43
    neg1cn
    a1i
    @10
    cc0
    wne
    @43
    neg1ne0
    a1i
    @43
    @12
    @14
    @43
    c2
    @11
    cdvds
    wbr
    #
    @12
    cz
    wcel
    #
    @43
    @28
    @1
    c1
    cz
    wcel
    #
    c2
    c1
    cdvds
    wbr
    wn
    #
    @44
    @0
    @28
    @1
    @5
    @42
    @32
    ad3antrrr
    #
    @0
    @1
    @5
    @42
    simpllr
    @43
    1zzd
    #
    c2
    cprime
    wcel
    @47
    @43
    2prm
    c2
    nprmdvds1
    mp1i
    #
    cM
    c1
    omoe
    syl22anc
    @43
    c2
    cz
    wcel
    #
    c2
    cc0
    wne
    #
    @11
    cz
    wcel
    #
    @44
    @45
    wb
    @51
    @43
    2z
    a1i
    #
    @52
    @43
    2ne0
    a1i
    #
    @43
    @28
    @53
    @48
    cM
    peano2zm
    syl
    c2
    @11
    dvdsval2
    syl3anc
    mpbid
    @43
    c2
    @13
    cdvds
    wbr
    #
    @14
    cz
    wcel
    #
    @43
    @27
    @4
    @46
    @47
    @56
    @5
    @27
    @2
    @42
    @3
    @27
    @4
    @30
    adantr
    ad2antlr
    #
    @2
    @3
    @4
    @42
    simplrr
    @49
    @50
    cN
    c1
    omoe
    syl22anc
    @43
    @51
    @52
    @13
    cz
    wcel
    #
    @56
    @57
    wb
    @54
    @55
    @43
    @27
    @59
    @58
    cN
    peano2zm
    syl
    c2
    @13
    dvdsval2
    syl3anc
    mpbid
    zmulcld
    expclzd
    mul01d
    @43
    @17
    cc0
    @16
    cmul
    @6
    @42
    @17
    cc0
    wceq
    #
    @0
    @3
    @42
    @60
    wb
    @1
    @4
    @0
    @3
    wa
    @8
    @17
    cc0
    @3
    @27
    @28
    @17
    cc0
    wne
    #
    @8
    wb
    @0
    @30
    @32
    @27
    @28
    wa
    #
    @61
    @37
    @8
    cN
    cM
    lgsne0
    @62
    @36
    @7
    c1
    @38
    eqeq1d
    bitrd
    syl2anr
    necon1bbid
    ad2ant2r
    biimpa
    oveq2d
    @6
    @42
    @9
    cc0
    wceq
    #
    @0
    @3
    @42
    @63
    wb
    #
    @1
    @4
    @0
    @28
    @27
    @64
    @3
    @32
    @30
    @28
    @27
    wa
    @8
    @9
    cc0
    cM
    cN
    lgsne0
    necon1bbid
    syl2an
    ad2ant2r
    biimpa
    3eqtr4rd
    pm2.61dan
end
