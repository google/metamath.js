include "cword.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "ccsh.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "chash.mm"
include "cfv.mm"
include "cv.mm"
include "cc0.mm"
include "cfzo.mm"
include "wral.mm"
include "wa.mm"
include "cshwlen.mm"
include "3adant3.mm"
include "cshwcl.mm"
include "anim1i.mm"
include "3adant2.mm"
include "syl.mm"
include "simp1.mm"
include "zaddcl.mm"
include "3adant1.mm"
include "jca.mm"
include "3eqtr4d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "cmo.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "simp3.mm"
include "eqcomd.mm"
include "biimpa.mm"
include "cshwidxmod.mm"
include "syl3anc.mm"
include "simpl2.mm"
include "cn.mm"
include "cn0.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "elfzo0.mm"
include "nn0z.mm"
include "ad2antrr.mm"
include "adantl.mm"
include "zaddcld.mm"
include "simpr.mm"
include "ex.mm"
include "sylbi.mm"
include "impcom.mm"
include "zmodfzo.mm"
include "wb.mm"
include "eleq1d.mm"
include "mpbird.mm"
include "cr.mm"
include "crp.mm"
include "nn0re.mm"
include "zre.mm"
include "ad2antll.mm"
include "readdcld.mm"
include "ad2antrl.mm"
include "nnrp.mm"
include "modaddmod.mm"
include "cc.mm"
include "nn0cn.mm"
include "zcn.mm"
include "add32r.mm"
include "oveq1d.mm"
include "com12.mm"
include "imp.mm"
include "fveq2d.mm"
include "3eqtrd.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "eqwrd.mm"

theorem 2cshw
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let vi: setvar i


  assert |- ( ( W e. Word V /\ M e. ZZ /\ N e. ZZ ) -> ( ( W cyclShift M ) cyclShift N ) = ( W cyclShift ( M + N ) ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cW
    cM
    ccsh
    co
    #
    cN
    ccsh
    co
    #
    cW
    cM
    cN
    caddc
    co
    #
    ccsh
    co
    #
    wceq
    #
    @6
    chash
    cfv
    #
    @8
    chash
    cfv
    #
    wceq
    #
    vi
    cv
    #
    @6
    cfv
    #
    @13
    @8
    cfv
    #
    wceq
    #
    vi
    cc0
    @10
    cfzo
    co
    #
    wral
    #
    wa
    #
    @4
    @12
    @18
    @4
    @5
    chash
    cfv
    #
    cW
    chash
    cfv
    #
    @10
    @11
    @1
    @2
    @20
    @21
    wceq
    #
    @3
    cM
    cV
    cW
    cshwlen
    3adant3
    #
    @4
    @5
    @0
    wcel
    #
    @3
    wa
    #
    @10
    @20
    wceq
    @1
    @3
    @25
    @2
    @1
    @24
    @3
    cM
    cV
    cW
    cshwcl
    #
    anim1i
    3adant2
    cN
    cV
    @5
    cshwlen
    syl
    #
    @4
    @1
    @7
    cz
    wcel
    #
    wa
    @11
    @21
    wceq
    @4
    @1
    @28
    @1
    @2
    @3
    simp1
    #
    @2
    @3
    @28
    @1
    cM
    cN
    zaddcl
    3adant1
    #
    jca
    @7
    cV
    cW
    cshwlen
    syl
    3eqtr4d
    @4
    @16
    vi
    @17
    @4
    @13
    @17
    wcel
    @13
    cc0
    @21
    cfzo
    co
    #
    wcel
    #
    @16
    @4
    @17
    @31
    @13
    @4
    @10
    @21
    cc0
    cfzo
    @4
    @10
    @20
    @21
    @27
    @23
    eqtrd
    oveq2d
    eleq2d
    @4
    @32
    @16
    @4
    @32
    wa
    #
    @14
    @13
    cN
    caddc
    co
    #
    @20
    cmo
    co
    #
    @5
    cfv
    #
    @35
    cM
    caddc
    co
    #
    @21
    cmo
    co
    #
    cW
    cfv
    #
    @15
    @33
    @24
    @3
    @13
    cc0
    @20
    cfzo
    co
    #
    wcel
    #
    @14
    @36
    wceq
    @4
    @24
    @32
    @1
    @2
    @24
    @3
    @26
    3ad2ant1
    adantr
    @4
    @3
    @32
    @1
    @2
    @3
    simp3
    #
    adantr
    @4
    @32
    @41
    @4
    @31
    @40
    @13
    @4
    @21
    @20
    cc0
    cfzo
    @4
    @20
    @21
    @23
    eqcomd
    oveq2d
    eleq2d
    biimpa
    @13
    cN
    cV
    @5
    cshwidxmod
    syl3anc
    @33
    @1
    @2
    @35
    @31
    wcel
    #
    @36
    @39
    wceq
    @4
    @1
    @32
    @29
    adantr
    #
    @1
    @2
    @3
    @32
    simpl2
    @33
    @43
    @34
    @21
    cmo
    co
    #
    @31
    wcel
    #
    @33
    @34
    cz
    wcel
    #
    @21
    cn
    wcel
    #
    wa
    #
    @46
    @32
    @4
    @49
    @32
    @13
    cn0
    wcel
    #
    @48
    @13
    @21
    clt
    wbr
    #
    w3a
    #
    @4
    @49
    wi
    #
    @13
    @21
    elfzo0
    #
    @50
    @48
    @53
    @51
    @50
    @48
    wa
    #
    @4
    @49
    @55
    @4
    wa
    #
    @47
    @48
    @56
    @13
    cN
    @50
    @13
    cz
    wcel
    @48
    @4
    @13
    nn0z
    ad2antrr
    @4
    @3
    @55
    @42
    adantl
    zaddcld
    @55
    @48
    @4
    @50
    @48
    simpr
    adantr
    jca
    ex
    3adant3
    sylbi
    impcom
    @34
    @21
    zmodfzo
    syl
    @4
    @43
    @46
    wb
    @32
    @4
    @35
    @45
    @31
    @4
    @20
    @21
    @34
    cmo
    @23
    oveq2d
    eleq1d
    adantr
    mpbird
    @35
    cM
    cV
    cW
    cshwidxmod
    syl3anc
    @33
    @45
    cM
    caddc
    co
    #
    @21
    cmo
    co
    #
    cW
    cfv
    @13
    @7
    caddc
    co
    #
    @21
    cmo
    co
    #
    cW
    cfv
    #
    @39
    @15
    @33
    @58
    @60
    cW
    @4
    @32
    @58
    @60
    wceq
    #
    @2
    @3
    @32
    @62
    wi
    @1
    @32
    @2
    @3
    wa
    #
    @62
    @32
    @52
    @63
    @62
    wi
    #
    @54
    @50
    @48
    @64
    @51
    @55
    @63
    @62
    @55
    @63
    wa
    #
    @58
    @34
    cM
    caddc
    co
    #
    @21
    cmo
    co
    #
    @60
    @65
    @34
    cr
    wcel
    cM
    cr
    wcel
    #
    @21
    crp
    wcel
    #
    @58
    @67
    wceq
    @65
    @13
    cN
    @50
    @13
    cr
    wcel
    @48
    @63
    @13
    nn0re
    ad2antrr
    @3
    cN
    cr
    wcel
    @55
    @2
    cN
    zre
    ad2antll
    readdcld
    @2
    @68
    @55
    @3
    cM
    zre
    ad2antrl
    @55
    @69
    @63
    @48
    @69
    @50
    @21
    nnrp
    adantl
    adantr
    @34
    cM
    @21
    modaddmod
    syl3anc
    @65
    @66
    @59
    @21
    cmo
    @65
    @59
    @66
    @65
    @13
    cc
    wcel
    #
    cM
    cc
    wcel
    #
    cN
    cc
    wcel
    #
    @59
    @66
    wceq
    @50
    @70
    @48
    @63
    @13
    nn0cn
    ad2antrr
    @2
    @71
    @55
    @3
    cM
    zcn
    ad2antrl
    @3
    @72
    @55
    @2
    cN
    zcn
    ad2antll
    @13
    cM
    cN
    add32r
    syl3anc
    eqcomd
    oveq1d
    eqtrd
    ex
    3adant3
    sylbi
    com12
    3adant1
    imp
    fveq2d
    @33
    @38
    @58
    cW
    @33
    @37
    @57
    @21
    cmo
    @33
    @35
    @45
    cM
    caddc
    @33
    @20
    @21
    @34
    cmo
    @4
    @22
    @32
    @23
    adantr
    oveq2d
    oveq1d
    oveq1d
    fveq2d
    @33
    @1
    @28
    @32
    @15
    @61
    wceq
    @44
    @4
    @28
    @32
    @30
    adantr
    @4
    @32
    simpr
    @13
    @7
    cV
    cW
    cshwidxmod
    syl3anc
    3eqtr4d
    3eqtrd
    ex
    sylbid
    ralrimiv
    jca
    @4
    @6
    @0
    wcel
    #
    @8
    @0
    wcel
    #
    wa
    #
    @9
    @19
    wb
    @1
    @2
    @75
    @3
    @1
    @73
    @74
    @1
    @24
    @73
    @26
    cN
    cV
    @5
    cshwcl
    syl
    @7
    cV
    cW
    cshwcl
    jca
    3ad2ant1
    @6
    vi
    cV
    @8
    eqwrd
    syl
    mpbird
end
