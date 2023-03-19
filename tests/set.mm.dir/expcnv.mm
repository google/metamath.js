include "cn0.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cmpt.mm"
include "cc0.mm"
include "cli.mm"
include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "c1.mm"
include "cvv.mm"
include "cn.mm"
include "nnuz.mm"
include "1zzd.mm"
include "wcel.mm"
include "nn0ex.mm"
include "mptex.mm"
include "a1i.mm"
include "0cnd.mm"
include "cfv.mm"
include "nnnn0.mm"
include "oveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "simpr.mm"
include "oveq1d.mm"
include "sylan9eqr.mm"
include "0exp.mm"
include "adantl.mm"
include "eqtrd.mm"
include "climconst.mm"
include "wne.mm"
include "cabs.mm"
include "cdiv.mm"
include "cmin.mm"
include "cc.mm"
include "clt.mm"
include "crp.mm"
include "adantr.mm"
include "absrpcl.mm"
include "sylan.mm"
include "reclt1d.mm"
include "mpbid.mm"
include "cr.mm"
include "wb.mm"
include "1re.mm"
include "rpreccld.mm"
include "rpred.mm"
include "difrp.mm"
include "sylancr.mm"
include "rpcnd.mm"
include "divcnv.mm"
include "nnex.mm"
include "nndivre.mm"
include "eqeltrd.mm"
include "cz.mm"
include "nnz.mm"
include "rpexpcl.mm"
include "syl2an.mm"
include "cle.mm"
include "cmul.mm"
include "nnrp.mm"
include "rpmulcl.mm"
include "caddc.mm"
include "peano2re.mm"
include "lep1d.mm"
include "rpge0d.mm"
include "bernneq2.mm"
include "syl3anc.mm"
include "letrd.mm"
include "rpcnne0d.mm"
include "exprec.mm"
include "3expa.mm"
include "breqtrd.mm"
include "lerec2d.mm"
include "nncn.mm"
include "nnne0.mm"
include "jca.mm"
include "recdiv2.mm"
include "breqtrrd.mm"
include "3brtr4d.mm"
include "climsqz2.mm"
include "expcl.mm"
include "absexp.mm"
include "fveq2d.mm"
include "3eqtr4rd.mm"
include "climabs0.mm"
include "biimpar.mm"
include "syldan.mm"
include "pm2.61dane.mm"

theorem expcnv
  let wph: wff ph
  let cA: class A
  let vn: setvar n
  let vk: setvar k
  assume expcnv.1: |- ( ph -> A e. CC )
  assume expcnv.2: |- ( ph -> ( abs ` A ) < 1 )

  disjoint A n
  disjoint k n
  disjoint A k
  disjoint k ph
  assert |- ( ph -> ( n e. NN0 |-> ( A ^ n ) ) ~~> 0 )

  proof
    wph
    vn
    cn0
    cA
    vn
    cv
    #
    cexp
    co
    #
    cmpt
    #
    cc0
    cli
    wbr
    #
    cA
    cc0
    wph
    cA
    cc0
    wceq
    #
    wa
    #
    cc0
    vk
    @2
    c1
    cvv
    cn
    nnuz
    @5
    1zzd
    @2
    cvv
    wcel
    #
    @5
    vn
    cn0
    @1
    nn0ex
    mptex
    #
    a1i
    @5
    0cnd
    @5
    vk
    cv
    #
    cn
    wcel
    #
    wa
    @8
    @2
    cfv
    #
    cc0
    @8
    cexp
    co
    #
    cc0
    @9
    @5
    @10
    cA
    @8
    cexp
    co
    #
    @11
    @9
    @8
    cn0
    wcel
    #
    @10
    @12
    wceq
    #
    @8
    nnnn0
    #
    vn
    @8
    @1
    @12
    cn0
    @2
    @0
    @8
    cA
    cexp
    oveq2
    @2
    eqid
    cA
    @8
    cexp
    ovex
    fvmpt
    #
    syl
    @5
    cA
    cc0
    @8
    cexp
    wph
    @4
    simpr
    oveq1d
    sylan9eqr
    @9
    @11
    cc0
    wceq
    @5
    @8
    0exp
    adantl
    eqtrd
    climconst
    wph
    cA
    cc0
    wne
    #
    vn
    cn
    cA
    cabs
    cfv
    #
    @0
    cexp
    co
    #
    cmpt
    #
    cc0
    cli
    wbr
    #
    @3
    wph
    @17
    wa
    #
    cc0
    vk
    vn
    cn
    c1
    c1
    @18
    cdiv
    co
    #
    c1
    cmin
    co
    #
    cdiv
    co
    #
    @0
    cdiv
    co
    #
    cmpt
    #
    @20
    c1
    cvv
    cn
    nnuz
    @22
    1zzd
    @22
    @25
    cc
    wcel
    @27
    cc0
    cli
    wbr
    @22
    @25
    @22
    @24
    @22
    c1
    @23
    clt
    wbr
    #
    @24
    crp
    wcel
    #
    @22
    @18
    c1
    clt
    wbr
    #
    @28
    wph
    @30
    @17
    expcnv.2
    adantr
    @22
    @18
    wph
    cA
    cc
    wcel
    #
    @17
    @18
    crp
    wcel
    #
    expcnv.1
    cA
    absrpcl
    sylan
    #
    reclt1d
    mpbid
    @22
    c1
    cr
    wcel
    @23
    cr
    wcel
    #
    @28
    @29
    wb
    1re
    @22
    @23
    @22
    @18
    @33
    rpreccld
    #
    rpred
    #
    c1
    @23
    difrp
    sylancr
    mpbid
    #
    rpreccld
    #
    rpcnd
    @25
    vn
    divcnv
    syl
    @20
    cvv
    wcel
    #
    @22
    vn
    cn
    @19
    nnex
    mptex
    #
    a1i
    @22
    @9
    wa
    #
    @8
    @27
    cfv
    #
    @25
    @8
    cdiv
    co
    #
    cr
    @9
    @42
    @43
    wceq
    @22
    vn
    @8
    @26
    @43
    cn
    @27
    @0
    @8
    @25
    cdiv
    oveq2
    @27
    eqid
    @25
    @8
    cdiv
    ovex
    fvmpt
    adantl
    #
    @22
    @25
    cr
    wcel
    @9
    @43
    cr
    wcel
    @22
    @25
    @38
    rpred
    @25
    @8
    nndivre
    sylan
    eqeltrd
    @41
    @8
    @20
    cfv
    #
    @41
    @45
    @18
    @8
    cexp
    co
    #
    crp
    @9
    @45
    @46
    wceq
    #
    @22
    vn
    @8
    @19
    @46
    cn
    @20
    @0
    @8
    @18
    cexp
    oveq2
    @20
    eqid
    @18
    @8
    cexp
    ovex
    fvmpt
    #
    adantl
    #
    @22
    @32
    @8
    cz
    wcel
    #
    @46
    crp
    wcel
    @9
    @33
    @8
    nnz
    #
    @18
    @8
    rpexpcl
    syl2an
    #
    eqeltrd
    #
    rpred
    @41
    @46
    @43
    @45
    @42
    cle
    @41
    @46
    c1
    @24
    @8
    cmul
    co
    #
    cdiv
    co
    #
    @43
    cle
    @41
    @54
    @46
    @22
    @29
    @8
    crp
    wcel
    @54
    crp
    wcel
    @9
    @37
    @8
    nnrp
    @24
    @8
    rpmulcl
    syl2an
    #
    @52
    @41
    @54
    @23
    @8
    cexp
    co
    #
    c1
    @46
    cdiv
    co
    #
    cle
    @41
    @54
    @54
    c1
    caddc
    co
    #
    @57
    @41
    @54
    @56
    rpred
    #
    @41
    @54
    cr
    wcel
    @59
    cr
    wcel
    @60
    @54
    peano2re
    syl
    @41
    @57
    @22
    @23
    crp
    wcel
    @50
    @57
    crp
    wcel
    @9
    @35
    @51
    @23
    @8
    rpexpcl
    syl2an
    rpred
    @41
    @54
    @60
    lep1d
    @41
    @34
    @13
    cc0
    @23
    cle
    wbr
    #
    @59
    @57
    cle
    wbr
    @22
    @34
    @9
    @36
    adantr
    @9
    @13
    @22
    @15
    adantl
    @22
    @61
    @9
    @22
    @23
    @35
    rpge0d
    adantr
    @23
    @8
    bernneq2
    syl3anc
    letrd
    @22
    @18
    cc
    wcel
    #
    @18
    cc0
    wne
    #
    wa
    @50
    @57
    @58
    wceq
    #
    @9
    @22
    @18
    @33
    rpcnne0d
    @51
    @62
    @63
    @50
    @64
    @18
    @8
    exprec
    3expa
    syl2an
    breqtrd
    lerec2d
    @22
    @24
    cc
    wcel
    @24
    cc0
    wne
    wa
    @8
    cc
    wcel
    #
    @8
    cc0
    wne
    #
    wa
    @43
    @55
    wceq
    @9
    @22
    @24
    @37
    rpcnne0d
    @9
    @65
    @66
    @8
    nncn
    @8
    nnne0
    jca
    @24
    @8
    recdiv2
    syl2an
    breqtrrd
    @49
    @44
    3brtr4d
    @41
    @45
    @53
    rpge0d
    climsqz2
    wph
    @3
    @21
    wph
    vk
    @2
    @20
    c1
    cvv
    cvv
    cn
    nnuz
    wph
    1zzd
    @6
    wph
    @7
    a1i
    @39
    wph
    @40
    a1i
    wph
    @9
    wa
    #
    @10
    @12
    cc
    @67
    @13
    @14
    @9
    @13
    wph
    @15
    adantl
    @16
    syl
    #
    wph
    @31
    @13
    @12
    cc
    wcel
    @9
    expcnv.1
    @15
    cA
    @8
    expcl
    syl2an
    eqeltrd
    @67
    @12
    cabs
    cfv
    #
    @46
    @10
    cabs
    cfv
    @45
    wph
    @31
    @13
    @69
    @46
    wceq
    @9
    expcnv.1
    @15
    cA
    @8
    absexp
    syl2an
    @67
    @10
    @12
    cabs
    @68
    fveq2d
    @9
    @47
    wph
    @48
    adantl
    3eqtr4rd
    climabs0
    biimpar
    syldan
    pm2.61dane
end
