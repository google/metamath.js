include "c1.mm"
include "wceq.mm"
include "cc0.mm"
include "cfv.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cfzo.mm"
include "co.mm"
include "wral.mm"
include "wi.mm"
include "c0.mm"
include "ral0.mm"
include "oveq2.mm"
include "fzo0.mm"
include "syl6eq.mm"
include "raleqdv.mm"
include "mpbiri.mm"
include "a1d.mm"
include "wn.mm"
include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cn0.mm"
include "cfz.mm"
include "nnnn0d.mm"
include "0elfz.mm"
include "syl.mm"
include "iccpartxr.mm"
include "adantr.mm"
include "cr.mm"
include "cpnf.mm"
include "cmnf.mm"
include "w3o.mm"
include "elxr.mm"
include "0zd.mm"
include "caddc.mm"
include "cuz.mm"
include "elfzouz.mm"
include "0p1e1.mm"
include "fveq2i.mm"
include "syl6eleqr.mm"
include "adantl.mm"
include "fveq2.mm"
include "eqcomd.mm"
include "eleq1d.mm"
include "biimpcd.mm"
include "ad3antrrr.mm"
include "wne.mm"
include "cn.mm"
include "ciccp.mm"
include "cle.mm"
include "w3a.mm"
include "elfz2nn0.mm"
include "cz.mm"
include "elfzo2.mm"
include "simpl1.mm"
include "simpr2.mm"
include "nn0ge0.mm"
include "0red.mm"
include "eluzelre.mm"
include "zre.mm"
include "lelttr.mm"
include "syl3anc.mm"
include "expcomd.mm"
include "3impia.mm"
include "syl5com.mm"
include "3ad2ant2.mm"
include "imp.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "nn0re.mm"
include "ad2antrl.mm"
include "expd.mm"
include "exp31.mm"
include "com34.mm"
include "com35.mm"
include "3imp.mm"
include "expdcom.mm"
include "3imp1.mm"
include "elfzo0.mm"
include "syl3anbrc.mm"
include "ex.mm"
include "syl5bi.mm"
include "sylbi.mm"
include "impcom.mm"
include "simpr.mm"
include "fzo1fzo0n0.mm"
include "iccpartipre.mm"
include "exp32.mm"
include "expdimp.mm"
include "pm2.61dne.mm"
include "cmin.mm"
include "cmap.mm"
include "ad3antlr.mm"
include "elfzoelz.mm"
include "fzoval.mm"
include "eleq2d.mm"
include "wss.mm"
include "elfzouz2.mm"
include "fzoss2.mm"
include "sseld.mm"
include "sylbid.mm"
include "iccpartimp.mm"
include "simprd.mm"
include "smonoord.mm"
include "ralrimiva.mm"
include "lbfzo0.mm"
include "sylibr.mm"
include "3jca.mm"
include "wb.mm"
include "breq1.mm"
include "mpbid.mm"
include "1nn0.mm"
include "a1i.mm"
include "nnnn0.mm"
include "nnge1.mm"
include "syl5eqel.mm"
include "pnfnlt.mm"
include "pm2.21dd.mm"
include "mnflt.mm"
include "ralbidv.mm"
include "mpbird.mm"
include "3jaoi.mm"
include "mpcom.mm"
include "expcom.mm"
include "pm2.61i.mm"

theorem iccpartigtl
  let wph: wff ph
  let cP: class P
  let vi: setvar i
  let cM: class M
  let vk: setvar k
  let vx: setvar x
  assume iccpartgtprec.m: |- ( ph -> M e. NN )
  assume iccpartgtprec.p: |- ( ph -> P e. ( RePart ` M ) )

  disjoint M i
  disjoint P i
  disjoint i ph
  disjoint M k
  disjoint i k
  disjoint P k
  disjoint k ph
  disjoint k x
  assert |- ( ph -> A. i e. ( 1 ..^ M ) ( P ` 0 ) < ( P ` i ) )

  proof
    cM
    c1
    wceq
    #
    wph
    cc0
    cP
    cfv
    #
    vi
    cv
    #
    cP
    cfv
    #
    clt
    wbr
    #
    vi
    c1
    cM
    cfzo
    co
    #
    wral
    #
    wi
    @0
    @6
    wph
    @0
    @6
    @4
    vi
    c0
    wral
    @4
    vi
    ral0
    @0
    @4
    vi
    @5
    c0
    @0
    @5
    c1
    c1
    cfzo
    co
    c0
    cM
    c1
    c1
    cfzo
    oveq2
    c1
    fzo0
    syl6eq
    raleqdv
    mpbiri
    a1d
    wph
    @0
    wn
    #
    @6
    @1
    cxr
    wcel
    #
    wph
    @7
    wa
    #
    @6
    wph
    @8
    @7
    wph
    cP
    cc0
    cM
    iccpartgtprec.m
    iccpartgtprec.p
    wph
    cM
    cn0
    wcel
    #
    cc0
    cc0
    cM
    cfz
    co
    #
    wcel
    wph
    cM
    iccpartgtprec.m
    nnnn0d
    cM
    0elfz
    syl
    iccpartxr
    adantr
    @8
    @1
    cr
    wcel
    #
    @1
    cpnf
    wceq
    #
    @1
    cmnf
    wceq
    #
    w3o
    @9
    @6
    wi
    #
    @1
    elxr
    @12
    @15
    @13
    @14
    @12
    @9
    @6
    @12
    @9
    wa
    #
    @4
    vi
    @5
    @16
    @2
    @5
    wcel
    #
    wa
    #
    vk
    cP
    cc0
    @2
    @18
    0zd
    @17
    @2
    cc0
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    @16
    @17
    @2
    c1
    cuz
    cfv
    #
    @20
    @2
    c1
    cM
    elfzouz
    @19
    c1
    cuz
    0p1e1
    fveq2i
    syl6eleqr
    adantl
    @18
    vk
    cv
    #
    cc0
    @2
    cfz
    co
    wcel
    #
    wa
    @22
    cP
    cfv
    #
    cr
    wcel
    #
    @22
    cc0
    @12
    @22
    cc0
    wceq
    #
    @25
    wi
    @9
    @17
    @23
    @26
    @12
    @25
    @26
    @1
    @24
    cr
    @26
    @24
    @1
    @22
    cc0
    cP
    fveq2
    eqcomd
    eleq1d
    biimpcd
    ad3antrrr
    @18
    @23
    @22
    cc0
    wne
    #
    @25
    @16
    @17
    @23
    @27
    wa
    #
    @25
    wi
    #
    wph
    @17
    @29
    wi
    @12
    @7
    wph
    @17
    @28
    @25
    wph
    @17
    @28
    wa
    #
    wa
    cP
    @22
    cM
    wph
    cM
    cn
    wcel
    #
    @30
    iccpartgtprec.m
    adantr
    wph
    cP
    cM
    ciccp
    cfv
    wcel
    #
    @30
    iccpartgtprec.p
    adantr
    @30
    @22
    @5
    wcel
    #
    wph
    @30
    @22
    cc0
    cM
    cfzo
    co
    #
    wcel
    #
    @27
    @33
    @28
    @17
    @35
    @23
    @17
    @35
    wi
    #
    @27
    @23
    @22
    cn0
    wcel
    #
    @2
    cn0
    wcel
    #
    @22
    @2
    cle
    wbr
    #
    w3a
    #
    @36
    @22
    @2
    elfz2nn0
    @17
    @2
    @21
    wcel
    #
    cM
    cz
    wcel
    #
    @2
    cM
    clt
    wbr
    #
    w3a
    #
    @40
    @35
    @2
    c1
    cM
    elfzo2
    @40
    @44
    @35
    @40
    @44
    wa
    #
    @37
    @31
    @22
    cM
    clt
    wbr
    #
    @35
    @37
    @38
    @39
    @44
    simpl1
    @45
    @42
    cc0
    cM
    clt
    wbr
    #
    @31
    @40
    @41
    @42
    @43
    simpr2
    @40
    @44
    @47
    @38
    @37
    @44
    @47
    wi
    @39
    @38
    cc0
    @2
    cle
    wbr
    #
    @44
    @47
    @2
    nn0ge0
    @41
    @42
    @43
    @48
    @47
    wi
    @41
    @42
    wa
    #
    @48
    @43
    @47
    @49
    cc0
    cr
    wcel
    @2
    cr
    wcel
    #
    cM
    cr
    wcel
    #
    @48
    @43
    wa
    @47
    wi
    @49
    0red
    @41
    @50
    @42
    c1
    @2
    eluzelre
    adantr
    @42
    @51
    @41
    cM
    zre
    adantl
    #
    cc0
    @2
    cM
    lelttr
    syl3anc
    expcomd
    3impia
    syl5com
    3ad2ant2
    imp
    cM
    elnnz
    sylanbrc
    @37
    @38
    @39
    @44
    @46
    @37
    @38
    @44
    @39
    @46
    @44
    @37
    @38
    @39
    @46
    wi
    #
    @41
    @42
    @43
    @37
    @38
    wa
    #
    @53
    wi
    @41
    @42
    @39
    @54
    @43
    @46
    @41
    @42
    @54
    @39
    @43
    @46
    wi
    #
    @41
    @42
    @54
    @39
    @55
    wi
    #
    @49
    @54
    wa
    @22
    cr
    wcel
    #
    @50
    @51
    @56
    @37
    @57
    @49
    @38
    @22
    nn0re
    ad2antrl
    @54
    @50
    @49
    @38
    @50
    @37
    @2
    nn0re
    adantl
    adantl
    @49
    @51
    @54
    @52
    adantr
    @57
    @50
    @51
    w3a
    @39
    @43
    @46
    @22
    @2
    cM
    lelttr
    expd
    syl3anc
    exp31
    com34
    com35
    3imp
    expdcom
    com34
    3imp1
    @22
    cM
    elfzo0
    syl3anbrc
    ex
    syl5bi
    sylbi
    adantr
    impcom
    @28
    @27
    @17
    @23
    @27
    simpr
    adantl
    @22
    cM
    fzo1fzo0n0
    sylanbrc
    adantl
    iccpartipre
    exp32
    ad2antrl
    imp
    expdimp
    pm2.61dne
    @18
    @22
    cc0
    @2
    c1
    cmin
    co
    cfz
    co
    #
    wcel
    #
    wa
    #
    cP
    cxr
    @11
    cmap
    co
    wcel
    #
    @24
    @22
    c1
    caddc
    co
    cP
    cfv
    clt
    wbr
    #
    @60
    @31
    @32
    @35
    @61
    @62
    wa
    @9
    @31
    @12
    @17
    @59
    wph
    @31
    @7
    iccpartgtprec.m
    adantr
    ad3antlr
    @9
    @32
    @12
    @17
    @59
    wph
    @32
    @7
    iccpartgtprec.p
    adantr
    ad3antlr
    @18
    @59
    @35
    @18
    @59
    @22
    cc0
    @2
    cfzo
    co
    #
    wcel
    @35
    @18
    @58
    @63
    @22
    @18
    @2
    cz
    wcel
    #
    @58
    @63
    wceq
    @17
    @64
    @16
    @2
    c1
    cM
    elfzoelz
    adantl
    @64
    @63
    @58
    cc0
    @2
    fzoval
    eqcomd
    syl
    eleq2d
    @18
    @63
    @34
    @22
    @18
    cM
    @2
    cuz
    cfv
    wcel
    #
    @63
    @34
    wss
    @17
    @65
    @16
    @2
    c1
    cM
    elfzouz2
    adantl
    @2
    cc0
    cM
    fzoss2
    syl
    sseld
    sylbid
    imp
    cP
    @22
    cM
    iccpartimp
    syl3anc
    simprd
    smonoord
    ralrimiva
    ex
    @13
    @9
    @6
    @13
    @9
    wa
    #
    @4
    vi
    @5
    @66
    @17
    wa
    #
    cpnf
    @19
    cP
    cfv
    #
    clt
    wbr
    #
    @4
    @67
    @1
    @68
    clt
    wbr
    #
    @69
    @67
    @61
    @70
    @67
    @31
    @32
    cc0
    @34
    wcel
    #
    w3a
    #
    @61
    @70
    wa
    @66
    @72
    @17
    wph
    @72
    @13
    @7
    wph
    @31
    @32
    @71
    iccpartgtprec.m
    iccpartgtprec.p
    wph
    @31
    @71
    iccpartgtprec.m
    cM
    lbfzo0
    sylibr
    3jca
    ad2antrl
    adantr
    cP
    cc0
    cM
    iccpartimp
    syl
    simprd
    @66
    @70
    @69
    wb
    #
    @17
    @13
    @73
    @9
    @1
    cpnf
    @68
    clt
    breq1
    adantr
    adantr
    mpbid
    @67
    @68
    cxr
    wcel
    @69
    wn
    @67
    cP
    @19
    cM
    @66
    @31
    @17
    wph
    @31
    @13
    @7
    iccpartgtprec.m
    ad2antrl
    adantr
    @66
    @32
    @17
    wph
    @32
    @13
    @7
    iccpartgtprec.p
    ad2antrl
    adantr
    @66
    @19
    @11
    wcel
    #
    @17
    wph
    @74
    @13
    @7
    wph
    @19
    c1
    @11
    0p1e1
    wph
    c1
    cn0
    wcel
    #
    @10
    c1
    cM
    cle
    wbr
    #
    w3a
    #
    c1
    @11
    wcel
    wph
    @31
    @77
    iccpartgtprec.m
    @31
    @75
    @10
    @76
    @75
    @31
    1nn0
    a1i
    cM
    nnnn0
    cM
    nnge1
    3jca
    syl
    c1
    cM
    elfz2nn0
    sylibr
    syl5eqel
    ad2antrl
    adantr
    iccpartxr
    @68
    pnfnlt
    syl
    pm2.21dd
    ralrimiva
    ex
    @14
    @9
    @6
    @14
    @9
    wa
    #
    @6
    cmnf
    @3
    clt
    wbr
    #
    vi
    @5
    wral
    #
    wph
    @80
    @14
    @7
    wph
    @79
    vi
    @5
    wph
    @17
    wa
    #
    @3
    cr
    wcel
    @79
    @81
    cP
    @2
    cM
    wph
    @31
    @17
    iccpartgtprec.m
    adantr
    wph
    @32
    @17
    iccpartgtprec.p
    adantr
    wph
    @17
    simpr
    iccpartipre
    @3
    mnflt
    syl
    ralrimiva
    ad2antrl
    @78
    @4
    @79
    vi
    @5
    @14
    @4
    @79
    wb
    @9
    @1
    cmnf
    @3
    clt
    breq1
    adantr
    ralbidv
    mpbird
    ex
    3jaoi
    sylbi
    mpcom
    expcom
    pm2.61i
end
