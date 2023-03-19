include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "csn.mm"
include "c1.mm"
include "cun.mm"
include "caddc.mm"
include "cuz.mm"
include "wceq.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "elnn0uz.mm"
include "sylib.mm"
include "fzpred.mm"
include "syl.mm"
include "0p1e1.mm"
include "oveq1i.mm"
include "a1i.mm"
include "uneq2d.mm"
include "eqtrd.mm"
include "eleq2d.mm"
include "wo.mm"
include "elun.mm"
include "velsn.mm"
include "orbi1i.mm"
include "bitri.mm"
include "cfzo.mm"
include "fzisfzounsn.mm"
include "orbi2i.mm"
include "syl6bb.mm"
include "wa.mm"
include "wral.mm"
include "wne.mm"
include "simpl.mm"
include "simpr.mm"
include "gt0ne0d.mm"
include "fzo1fzo0n0.mm"
include "sylanbrc.mm"
include "iccpartigtl.mm"
include "fveq2.mm"
include "breq2d.mm"
include "rspcv.mm"
include "syl2imc.mm"
include "expd.mm"
include "impcom.mm"
include "breq1.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "syl5ibr.mm"
include "com12.mm"
include "iccpartlt.mm"
include "breqan12rd.mm"
include "a1dd.mm"
include "ex.mm"
include "jaoi.mm"
include "cz.mm"
include "elfzelz.mm"
include "ad3antlr.mm"
include "cle.mm"
include "w3a.mm"
include "peano2zd.mm"
include "ad2antlr.mm"
include "elfzoelz.mm"
include "ad2antrr.mm"
include "wb.mm"
include "anim12ci.mm"
include "adantr.mm"
include "zltp1le.mm"
include "mpbid.mm"
include "3jca.mm"
include "eluz2.mm"
include "sylibr.mm"
include "cn.mm"
include "ciccp.mm"
include "1zzd.mm"
include "adantl.mm"
include "elfzle1.mm"
include "cr.mm"
include "1red.mm"
include "elfzel1.mm"
include "zred.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "syl5com.mm"
include "imp.mm"
include "syl3anbrc.mm"
include "elfzel2.mm"
include "ad4antr.mm"
include "nnred.mm"
include "elfzle2.mm"
include "elfzolt2.mm"
include "lelttrd.mm"
include "elfzo2.mm"
include "iccpartipre.mm"
include "cmin.mm"
include "cxr.mm"
include "cmap.mm"
include "ad3antrrr.mm"
include "fzoval.mm"
include "wss.mm"
include "elfzo0le.mm"
include "0le1.mm"
include "0red.mm"
include "mpani.mm"
include "mpd.mm"
include "0zd.mm"
include "elfzoel2.mm"
include "jca.mm"
include "ssfzo12bi.mm"
include "mpbird.mm"
include "eqsstr3d.mm"
include "sselda.mm"
include "iccpartimp.mm"
include "simprd.mm"
include "smonoord.mm"
include "exp31.mm"
include "com23.mm"
include "elfzuz.mm"
include "iccpartiltu.mm"
include "breq2.mm"
include "anbi2d.mm"
include "3imtr4d.mm"
include "exp4c.mm"
include "com13.mm"
include "sylbid.mm"
include "com3r.mm"
include "sylbi.mm"
include "imp32.mm"
include "ralrimivva.mm"

theorem iccpartgt
  let wph: wff ph
  let cP: class P
  let vi: setvar i
  let vj: setvar j
  let cM: class M
  let vk: setvar k
  let vx: setvar x
  assume iccpartgtprec.m: |- ( ph -> M e. NN )
  assume iccpartgtprec.p: |- ( ph -> P e. ( RePart ` M ) )

  disjoint M j
  disjoint P i
  disjoint P j
  disjoint i j
  disjoint j ph
  disjoint M i
  disjoint P i
  disjoint i ph
  disjoint M k
  disjoint j k
  disjoint M k
  disjoint i k
  disjoint P k
  disjoint k ph
  disjoint k x
  assert |- ( ph -> A. i e. ( 0 ... M ) A. j e. ( 0 ... M ) ( i < j -> ( P ` i ) < ( P ` j ) ) )

  proof
    wph
    vi
    cv
    #
    vj
    cv
    #
    clt
    wbr
    #
    @0
    cP
    cfv
    #
    @1
    cP
    cfv
    #
    clt
    wbr
    #
    wi
    #
    vi
    vj
    cc0
    cM
    cfz
    co
    #
    @7
    wph
    @0
    @7
    wcel
    #
    @1
    @7
    wcel
    #
    @6
    wph
    @8
    @0
    cc0
    csn
    #
    c1
    cM
    cfz
    co
    #
    cun
    #
    wcel
    #
    @9
    @6
    wi
    #
    wph
    @7
    @12
    @0
    wph
    @7
    @10
    cc0
    c1
    caddc
    co
    #
    cM
    cfz
    co
    #
    cun
    #
    @12
    wph
    cM
    cc0
    cuz
    cfv
    wcel
    #
    @7
    @17
    wceq
    wph
    cM
    cn0
    wcel
    @18
    wph
    cM
    iccpartgtprec.m
    nnnn0d
    cM
    elnn0uz
    sylib
    #
    cc0
    cM
    fzpred
    syl
    wph
    @16
    @11
    @10
    @16
    @11
    wceq
    wph
    @15
    c1
    cM
    cfz
    0p1e1
    oveq1i
    a1i
    uneq2d
    eqtrd
    eleq2d
    @13
    wph
    @14
    @13
    @0
    cc0
    wceq
    #
    @0
    @11
    wcel
    #
    wo
    #
    wph
    @14
    wi
    @13
    @0
    @10
    wcel
    #
    @21
    wo
    @22
    @0
    @10
    @11
    elun
    @23
    @20
    @21
    vi
    cc0
    velsn
    orbi1i
    bitri
    wph
    @9
    @22
    @6
    wph
    @9
    @1
    cc0
    cM
    cfzo
    co
    #
    wcel
    #
    @1
    cM
    wceq
    #
    wo
    #
    @22
    @6
    wi
    wph
    @9
    @1
    @24
    cM
    csn
    #
    cun
    #
    wcel
    #
    @27
    wph
    @7
    @29
    @1
    wph
    @18
    @7
    @29
    wceq
    @19
    cc0
    cM
    fzisfzounsn
    syl
    eleq2d
    @30
    @25
    @1
    @28
    wcel
    #
    wo
    @27
    @1
    @24
    @28
    elun
    @31
    @26
    @25
    vj
    cM
    velsn
    orbi2i
    bitri
    syl6bb
    @22
    @27
    wph
    @6
    @20
    @27
    wph
    @6
    wi
    #
    wi
    @21
    @27
    @20
    @32
    @25
    @20
    @32
    wi
    @26
    @20
    @25
    @32
    @20
    @25
    wph
    @6
    @25
    wph
    wa
    @6
    @20
    cc0
    @1
    clt
    wbr
    #
    cc0
    cP
    cfv
    #
    @4
    clt
    wbr
    #
    wi
    #
    wph
    @25
    @36
    wph
    @25
    @33
    @35
    @25
    @33
    wa
    #
    @1
    c1
    cM
    cfzo
    co
    #
    wcel
    #
    wph
    @34
    vk
    cv
    #
    cP
    cfv
    #
    clt
    wbr
    #
    vk
    @38
    wral
    @35
    @37
    @25
    @1
    cc0
    wne
    @39
    @25
    @33
    simpl
    @37
    @1
    @25
    @33
    simpr
    gt0ne0d
    @1
    cM
    fzo1fzo0n0
    sylanbrc
    wph
    cP
    vk
    cM
    iccpartgtprec.m
    iccpartgtprec.p
    iccpartigtl
    @42
    @35
    vk
    @1
    @38
    @40
    @1
    wceq
    @41
    @4
    @34
    clt
    @40
    @1
    cP
    fveq2
    breq2d
    rspcv
    syl2imc
    expd
    impcom
    @20
    @2
    @33
    @5
    @35
    @0
    cc0
    @1
    clt
    breq1
    @20
    @3
    @34
    @4
    clt
    @0
    cc0
    cP
    fveq2
    #
    breq1d
    imbi12d
    syl5ibr
    expd
    com12
    @26
    @20
    @32
    @26
    @20
    wa
    #
    wph
    @5
    @2
    wph
    @5
    @44
    @34
    cM
    cP
    cfv
    #
    clt
    wbr
    wph
    cP
    cM
    iccpartgtprec.m
    iccpartgtprec.p
    iccpartlt
    @20
    @26
    @3
    @34
    @4
    @45
    clt
    @43
    @1
    cM
    cP
    fveq2
    #
    breqan12rd
    syl5ibr
    a1dd
    ex
    jaoi
    com12
    @27
    @21
    @32
    @25
    @21
    @32
    wi
    @26
    @25
    @21
    @32
    @25
    @21
    wa
    #
    @2
    wph
    @5
    @47
    @2
    wph
    @5
    @47
    @2
    wa
    #
    wph
    wa
    #
    vk
    cP
    @0
    @1
    @21
    @0
    cz
    wcel
    #
    @25
    @2
    wph
    @0
    c1
    cM
    elfzelz
    #
    ad3antlr
    @49
    @0
    c1
    caddc
    co
    #
    cz
    wcel
    #
    @1
    cz
    wcel
    #
    @52
    @1
    cle
    wbr
    #
    w3a
    #
    @1
    @52
    cuz
    cfv
    wcel
    @48
    @56
    wph
    @48
    @53
    @54
    @55
    @21
    @53
    @25
    @2
    @21
    @0
    @51
    peano2zd
    ad2antlr
    @25
    @54
    @21
    @2
    @1
    cc0
    cM
    elfzoelz
    #
    ad2antrr
    @48
    @2
    @55
    @47
    @2
    simpr
    #
    @48
    @50
    @54
    wa
    #
    @2
    @55
    wb
    @47
    @59
    @2
    @25
    @54
    @21
    @50
    @57
    @51
    anim12ci
    adantr
    #
    @0
    @1
    zltp1le
    syl
    mpbid
    3jca
    adantr
    @52
    @1
    eluz2
    sylibr
    @49
    @40
    @0
    @1
    cfz
    co
    wcel
    #
    wa
    #
    cP
    @40
    cM
    wph
    cM
    cn
    wcel
    #
    @48
    @61
    iccpartgtprec.m
    ad2antlr
    #
    wph
    cP
    cM
    ciccp
    cfv
    wcel
    #
    @48
    @61
    iccpartgtprec.p
    ad2antlr
    @62
    @40
    c1
    cuz
    cfv
    #
    wcel
    #
    cM
    cz
    wcel
    #
    @40
    cM
    clt
    wbr
    @40
    @38
    wcel
    @62
    c1
    cz
    wcel
    @40
    cz
    wcel
    #
    c1
    @40
    cle
    wbr
    #
    @67
    @62
    1zzd
    @61
    @69
    @49
    @40
    @0
    @1
    elfzelz
    #
    adantl
    @49
    @61
    @70
    @21
    @61
    @70
    wi
    @25
    @2
    wph
    @21
    c1
    @0
    cle
    wbr
    #
    @61
    @70
    @0
    c1
    cM
    elfzle1
    #
    @61
    @72
    @0
    @40
    cle
    wbr
    #
    @70
    @40
    @0
    @1
    elfzle1
    @61
    c1
    cr
    wcel
    #
    @0
    cr
    wcel
    #
    @40
    cr
    wcel
    #
    @72
    @74
    wa
    @70
    wi
    @61
    1red
    @61
    @0
    @40
    @0
    @1
    elfzel1
    zred
    @61
    @40
    @71
    zred
    #
    c1
    @0
    @40
    letr
    syl3anc
    mpan2d
    syl5com
    ad3antlr
    imp
    c1
    @40
    eluz2
    syl3anbrc
    @48
    @68
    wph
    @61
    @21
    @68
    @25
    @2
    @0
    c1
    cM
    elfzel2
    #
    ad2antlr
    ad2antrr
    @62
    @40
    @1
    cM
    @61
    @77
    @49
    @78
    adantl
    @25
    @1
    cr
    wcel
    @21
    @2
    wph
    @61
    @25
    @1
    @57
    zred
    ad4antr
    @62
    cM
    @64
    nnred
    @61
    @40
    @1
    cle
    wbr
    @49
    @40
    @0
    @1
    elfzle2
    adantl
    @25
    @1
    cM
    clt
    wbr
    @21
    @2
    wph
    @61
    @1
    cc0
    cM
    elfzolt2
    ad4antr
    lelttrd
    @40
    c1
    cM
    elfzo2
    syl3anbrc
    iccpartipre
    @49
    @40
    @0
    @1
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
    @7
    cmap
    co
    wcel
    #
    @41
    @40
    c1
    caddc
    co
    cP
    cfv
    clt
    wbr
    #
    @82
    @63
    @65
    @40
    @24
    wcel
    @83
    @84
    wa
    wph
    @63
    @48
    @81
    iccpartgtprec.m
    ad2antlr
    wph
    @65
    @48
    @81
    iccpartgtprec.p
    ad2antlr
    @49
    @80
    @24
    @40
    @49
    @80
    @0
    @1
    cfzo
    co
    #
    @24
    @49
    @54
    @85
    @80
    wceq
    @25
    @54
    @21
    @2
    wph
    @57
    ad3antrrr
    @0
    @1
    fzoval
    syl
    @48
    @85
    @24
    wss
    #
    wph
    @48
    @86
    cc0
    @0
    cle
    wbr
    #
    @1
    cM
    cle
    wbr
    #
    wa
    #
    @47
    @89
    @2
    @25
    @88
    @21
    @87
    @1
    cM
    elfzo0le
    @21
    @72
    @87
    @73
    @21
    cc0
    c1
    cle
    wbr
    #
    @72
    @87
    0le1
    @21
    cc0
    cr
    wcel
    @75
    @76
    @90
    @72
    wa
    @87
    wi
    @21
    0red
    @21
    1red
    @21
    @0
    @51
    zred
    cc0
    c1
    @0
    letr
    syl3anc
    mpani
    mpd
    anim12ci
    adantr
    @48
    @59
    cc0
    cz
    wcel
    #
    @68
    wa
    #
    @2
    @86
    @89
    wb
    @60
    @25
    @92
    @21
    @2
    @25
    @91
    @68
    @25
    0zd
    @1
    cc0
    cM
    elfzoel2
    jca
    ad2antrr
    @58
    @0
    @1
    cc0
    cM
    ssfzo12bi
    syl3anc
    mpbird
    adantr
    eqsstr3d
    sselda
    cP
    @40
    cM
    iccpartimp
    syl3anc
    simprd
    smonoord
    exp31
    com23
    ex
    @26
    @21
    wph
    @2
    @5
    @26
    @21
    wph
    wa
    #
    @0
    cM
    clt
    wbr
    #
    wa
    #
    @3
    @45
    clt
    wbr
    #
    @93
    @2
    wa
    @5
    @95
    @96
    wi
    @26
    @93
    @94
    @96
    wph
    @21
    @94
    @96
    wi
    wph
    @21
    @94
    @96
    @21
    @94
    wa
    #
    @0
    @38
    wcel
    #
    wph
    @41
    @45
    clt
    wbr
    #
    vk
    @38
    wral
    @96
    @97
    @0
    @66
    wcel
    #
    @68
    @94
    @98
    @21
    @100
    @94
    @0
    c1
    cM
    elfzuz
    adantr
    @21
    @68
    @94
    @79
    adantr
    @21
    @94
    simpr
    @0
    c1
    cM
    elfzo2
    syl3anbrc
    wph
    cP
    vk
    cM
    iccpartgtprec.m
    iccpartgtprec.p
    iccpartiltu
    @99
    @96
    vk
    @0
    @38
    @40
    @0
    wceq
    @41
    @3
    @45
    clt
    @40
    @0
    cP
    fveq2
    breq1d
    rspcv
    syl2imc
    expd
    impcom
    imp
    a1i
    @26
    @2
    @94
    @93
    @1
    cM
    @0
    clt
    breq2
    anbi2d
    @26
    @4
    @45
    @3
    clt
    @46
    breq2d
    3imtr4d
    exp4c
    jaoi
    com12
    jaoi
    com13
    sylbid
    com3r
    sylbi
    com12
    sylbid
    imp32
    ralrimivva
end
