include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "wral.mm"
include "wceq.mm"
include "wi.mm"
include "c0.mm"
include "ral0.mm"
include "oveq2.mm"
include "fzo0.mm"
include "syl6eq.mm"
include "fveq2.mm"
include "breq2d.mm"
include "raleqbidv.mm"
include "mpbiri.mm"
include "2a1d.mm"
include "wn.mm"
include "wa.mm"
include "cxr.mm"
include "simpr.mm"
include "ciccp.mm"
include "adantr.mm"
include "cc0.mm"
include "cfz.mm"
include "cn0.mm"
include "nnnn0.mm"
include "nn0fz0.mm"
include "sylib.mm"
include "adantl.mm"
include "iccpartxr.mm"
include "cr.mm"
include "cpnf.mm"
include "cmnf.mm"
include "w3o.mm"
include "elxr.mm"
include "cz.mm"
include "elfzoelz.mm"
include "ad2antll.mm"
include "caddc.mm"
include "cuz.mm"
include "w3a.mm"
include "elfzo2.mm"
include "cle.mm"
include "eluzelz.mm"
include "peano2zd.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "wb.mm"
include "zltp1le.mm"
include "sylan.mm"
include "biimp3a.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "sylbi.mm"
include "eqcomd.mm"
include "eleq1d.mm"
include "biimpcd.mm"
include "com12.mm"
include "elfz2.mm"
include "1red.mm"
include "zre.mm"
include "letr.mm"
include "syl3anc.mm"
include "expcomd.mm"
include "adantrd.mm"
include "3adant2.mm"
include "imp.mm"
include "3ad2ant3.mm"
include "syl5bi.mm"
include "3adant3.mm"
include "wne.mm"
include "anim12ci.mm"
include "3adant1.mm"
include "ltlen.mm"
include "syl.mm"
include "nesym.mm"
include "anbi2i.mm"
include "syl6rbb.mm"
include "biimpd.mm"
include "expd.mm"
include "adantld.mm"
include "jca.mm"
include "elfzelz.mm"
include "1zzd.mm"
include "elfzel2.mm"
include "3jca.mm"
include "3ad2ant2.mm"
include "elfzo.mm"
include "mpbird.mm"
include "3exp.mm"
include "impcom.mm"
include "iccpartipre.mm"
include "ex.mm"
include "pm2.61i.mm"
include "cmin.mm"
include "cmap.mm"
include "wss.mm"
include "1eluzge0.mm"
include "fzoss1.mm"
include "mp1i.mm"
include "elfzoel2.mm"
include "fzoval.mm"
include "eleq2d.mm"
include "elfzouz.mm"
include "sseld.mm"
include "sylbid.mm"
include "sseldd.mm"
include "iccpartimp.mm"
include "simprd.mm"
include "smonoord.mm"
include "ltpnf.mm"
include "breq2.mm"
include "syl5ibr.mm"
include "elfzofz.mm"
include "elfzubelfz.mm"
include "iccpartgtprec.mm"
include "eqcoms.mm"
include "c2.mm"
include "nnne0.mm"
include "df-ne.mm"
include "biimpri.mm"
include "nn0n0n1ge2.mm"
include "ige2m1fz.mm"
include "nltmnf.mm"
include "pm2.21dd.mm"
include "3jaoi.mm"
include "impl.mm"
include "ralrimiva.mm"
include "mpcom.mm"
include "expcom.mm"
include "mpd.mm"

theorem iccpartiltu
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
  assert |- ( ph -> A. i e. ( 1 ..^ M ) ( P ` i ) < ( P ` M ) )

  proof
    wph
    cM
    cn
    wcel
    #
    vi
    cv
    #
    cP
    cfv
    #
    cM
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
    iccpartgtprec.m
    cM
    c1
    wceq
    #
    wph
    @0
    @6
    wi
    #
    wi
    @7
    @6
    wph
    @0
    @7
    @6
    @2
    c1
    cP
    cfv
    #
    clt
    wbr
    #
    vi
    c0
    wral
    @10
    vi
    ral0
    @7
    @4
    @10
    vi
    @5
    c0
    @7
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
    @7
    @3
    @9
    @2
    clt
    cM
    c1
    cP
    fveq2
    breq2d
    raleqbidv
    mpbiri
    2a1d
    wph
    @7
    wn
    #
    @8
    wph
    @11
    wa
    #
    @0
    @6
    @3
    cxr
    wcel
    #
    @12
    @0
    wa
    #
    @6
    @14
    cP
    cM
    cM
    @12
    @0
    simpr
    #
    @12
    cP
    cM
    ciccp
    cfv
    wcel
    #
    @0
    wph
    @16
    @11
    iccpartgtprec.p
    adantr
    adantr
    #
    @0
    cM
    cc0
    cM
    cfz
    co
    #
    wcel
    #
    @12
    @0
    cM
    cn0
    wcel
    #
    @19
    cM
    nnnn0
    #
    cM
    nn0fz0
    sylib
    adantl
    iccpartxr
    @13
    @3
    cr
    wcel
    #
    @3
    cpnf
    wceq
    #
    @3
    cmnf
    wceq
    #
    w3o
    #
    @14
    @6
    wi
    @3
    elxr
    @25
    @14
    @6
    @25
    @14
    wa
    @4
    vi
    @5
    @25
    @14
    @1
    @5
    wcel
    #
    @4
    @22
    @14
    @26
    wa
    #
    @4
    wi
    @23
    @24
    @22
    @27
    @4
    @22
    @27
    wa
    #
    vk
    cP
    @1
    cM
    @26
    @1
    cz
    wcel
    #
    @22
    @14
    @1
    c1
    cM
    elfzoelz
    ad2antll
    @26
    cM
    @1
    c1
    caddc
    co
    #
    cuz
    cfv
    wcel
    #
    @22
    @14
    @26
    @1
    c1
    cuz
    cfv
    wcel
    #
    cM
    cz
    wcel
    #
    @1
    cM
    clt
    wbr
    #
    w3a
    #
    @31
    @1
    c1
    cM
    elfzo2
    #
    @35
    @30
    cz
    wcel
    #
    @33
    @30
    cM
    cle
    wbr
    #
    @31
    @32
    @33
    @37
    @34
    @32
    @1
    c1
    @1
    eluzelz
    #
    peano2zd
    3ad2ant1
    @32
    @33
    @34
    simp2
    @32
    @33
    @34
    @38
    @32
    @29
    @33
    @34
    @38
    wb
    @39
    @1
    cM
    zltp1le
    sylan
    biimp3a
    @30
    cM
    eluz2
    syl3anbrc
    sylbi
    ad2antll
    vk
    cv
    #
    cM
    wceq
    #
    @28
    @40
    @1
    cM
    cfz
    co
    wcel
    #
    wa
    #
    @40
    cP
    cfv
    #
    cr
    wcel
    #
    wi
    @43
    @41
    @45
    @28
    @41
    @45
    wi
    #
    @42
    @22
    @46
    @27
    @41
    @22
    @45
    @41
    @3
    @44
    cr
    @41
    @44
    @3
    @40
    cM
    cP
    fveq2
    eqcomd
    eleq1d
    biimpcd
    adantr
    adantr
    com12
    @41
    wn
    #
    @43
    @45
    @47
    @43
    wa
    cP
    @40
    cM
    @43
    @0
    @47
    @28
    @0
    @42
    @27
    @0
    @22
    @14
    @0
    @26
    @15
    adantr
    #
    adantl
    #
    adantr
    adantl
    @43
    @16
    @47
    @28
    @16
    @42
    @27
    @16
    @22
    @14
    @16
    @26
    @17
    adantr
    #
    adantl
    #
    adantr
    adantl
    @43
    @47
    @40
    @5
    wcel
    #
    @28
    @42
    @47
    @52
    wi
    #
    @26
    @42
    @53
    wi
    @22
    @14
    @26
    @42
    @47
    @52
    @26
    @42
    @47
    w3a
    #
    @52
    c1
    @40
    cle
    wbr
    #
    @40
    cM
    clt
    wbr
    #
    wa
    #
    @54
    @55
    @56
    @26
    @42
    @55
    @47
    @26
    @42
    @55
    @42
    @29
    @33
    @40
    cz
    wcel
    #
    w3a
    #
    @1
    @40
    cle
    wbr
    #
    @40
    cM
    cle
    wbr
    #
    wa
    #
    wa
    #
    @26
    @55
    @40
    @1
    cM
    elfz2
    #
    @26
    @35
    @63
    @55
    wi
    #
    @36
    @32
    @33
    @65
    @34
    @32
    c1
    cz
    wcel
    #
    @29
    c1
    @1
    cle
    wbr
    #
    w3a
    @65
    c1
    @1
    eluz2
    @67
    @66
    @65
    @29
    @63
    @67
    @55
    @59
    @62
    @67
    @55
    wi
    #
    @29
    @58
    @62
    @68
    wi
    @33
    @29
    @58
    wa
    #
    @60
    @68
    @61
    @69
    @67
    @60
    @55
    @69
    c1
    cr
    wcel
    @1
    cr
    wcel
    #
    @40
    cr
    wcel
    #
    @67
    @60
    wa
    @55
    wi
    @69
    1red
    @29
    @70
    @58
    @1
    zre
    adantr
    @58
    @71
    @29
    @40
    zre
    #
    adantl
    c1
    @1
    @40
    letr
    syl3anc
    expcomd
    adantrd
    3adant2
    imp
    com12
    3ad2ant3
    sylbi
    3ad2ant1
    sylbi
    syl5bi
    imp
    3adant3
    @42
    @47
    @56
    @26
    @42
    @47
    @56
    @42
    @63
    @47
    @56
    wi
    #
    @64
    @59
    @62
    @73
    @59
    @61
    @73
    @60
    @59
    @61
    @47
    @56
    @59
    @61
    @47
    wa
    #
    @56
    @59
    @56
    @61
    cM
    @40
    wne
    #
    wa
    #
    @74
    @59
    @71
    cM
    cr
    wcel
    #
    wa
    #
    @56
    @76
    wb
    @33
    @58
    @78
    @29
    @33
    @77
    @58
    @71
    cM
    zre
    @72
    anim12ci
    3adant1
    @40
    cM
    ltlen
    syl
    @75
    @47
    @61
    cM
    @40
    nesym
    anbi2i
    syl6rbb
    biimpd
    expd
    adantld
    imp
    sylbi
    imp
    3adant1
    jca
    @54
    @58
    @66
    @33
    w3a
    #
    @52
    @57
    wb
    @42
    @26
    @79
    @47
    @42
    @58
    @66
    @33
    @40
    @1
    cM
    elfzelz
    @42
    1zzd
    @40
    @1
    cM
    elfzel2
    3jca
    3ad2ant2
    @40
    c1
    cM
    elfzo
    syl
    mpbird
    3exp
    ad2antll
    imp
    impcom
    iccpartipre
    ex
    pm2.61i
    @28
    @40
    @1
    cM
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    cP
    cxr
    @18
    cmap
    co
    wcel
    #
    @44
    @40
    c1
    caddc
    co
    cP
    cfv
    clt
    wbr
    #
    @83
    @0
    @16
    @40
    cc0
    cM
    cfzo
    co
    #
    wcel
    #
    @84
    @85
    wa
    @28
    @0
    @82
    @49
    adantr
    @28
    @16
    @82
    @51
    adantr
    @28
    @82
    @87
    @26
    @82
    @87
    wi
    @22
    @14
    @26
    @82
    @87
    @26
    @82
    wa
    #
    @5
    @86
    @40
    c1
    cc0
    cuz
    cfv
    wcel
    @5
    @86
    wss
    @88
    1eluzge0
    c1
    cc0
    cM
    fzoss1
    mp1i
    @26
    @82
    @52
    @26
    @82
    @40
    @1
    cM
    cfzo
    co
    #
    wcel
    @52
    @26
    @81
    @89
    @40
    @26
    @89
    @81
    @26
    @33
    @89
    @81
    wceq
    @1
    c1
    cM
    elfzoel2
    @1
    cM
    fzoval
    syl
    eqcomd
    eleq2d
    @26
    @89
    @5
    @40
    @26
    @32
    @89
    @5
    wss
    @1
    c1
    cM
    elfzouz
    @1
    c1
    cM
    fzoss1
    syl
    sseld
    sylbid
    imp
    sseldd
    ex
    ad2antll
    imp
    cP
    @40
    cM
    iccpartimp
    syl3anc
    simprd
    smonoord
    ex
    @27
    @4
    @23
    @2
    cpnf
    clt
    wbr
    #
    @27
    @2
    cr
    wcel
    @90
    @27
    cP
    @1
    cM
    @48
    @50
    @14
    @26
    simpr
    iccpartipre
    @2
    ltpnf
    syl
    @3
    cpnf
    @2
    clt
    breq2
    syl5ibr
    @24
    @27
    @4
    @24
    @27
    wa
    #
    @80
    cP
    cfv
    #
    cmnf
    clt
    wbr
    #
    @4
    @91
    @93
    @92
    @3
    clt
    wbr
    #
    @91
    cP
    cM
    cM
    @27
    @0
    @24
    @48
    adantl
    #
    @27
    @16
    @24
    @50
    adantl
    #
    @91
    @1
    c1
    cM
    cfz
    co
    #
    wcel
    #
    cM
    @97
    wcel
    @26
    @98
    @24
    @14
    @1
    c1
    cM
    elfzofz
    ad2antll
    @1
    c1
    cM
    elfzubelfz
    syl
    iccpartgtprec
    @24
    @93
    @94
    wb
    #
    @27
    @99
    cmnf
    @3
    cmnf
    @3
    @92
    clt
    breq2
    eqcoms
    adantr
    mpbird
    @91
    @92
    cxr
    wcel
    @93
    wn
    @91
    cP
    @80
    cM
    @95
    @96
    @91
    @20
    c2
    cM
    cle
    wbr
    #
    wa
    #
    @80
    @18
    wcel
    @27
    @101
    @24
    @27
    @20
    @100
    @14
    @20
    @26
    @0
    @20
    @12
    @21
    adantl
    #
    adantr
    @27
    @20
    cM
    cc0
    wne
    #
    cM
    c1
    wne
    #
    w3a
    #
    @100
    @14
    @105
    @26
    @14
    @20
    @103
    @104
    @102
    @0
    @103
    @12
    cM
    nnne0
    adantl
    @12
    @104
    @0
    @11
    @104
    wph
    @104
    @11
    cM
    c1
    df-ne
    biimpri
    adantl
    adantr
    3jca
    adantr
    cM
    nn0n0n1ge2
    syl
    jca
    adantl
    cM
    ige2m1fz
    syl
    iccpartxr
    @92
    nltmnf
    syl
    pm2.21dd
    ex
    3jaoi
    impl
    ralrimiva
    ex
    sylbi
    mpcom
    ex
    expcom
    pm2.61i
    mpd
end
