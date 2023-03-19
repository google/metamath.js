include "cfv.mm"
include "cfa.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cprod.mm"
include "cdiv.mm"
include "c1.mm"
include "cmin.mm"
include "clt.mm"
include "wbr.mm"
include "cexp.mm"
include "cmul.mm"
include "cif.mm"
include "csu.mm"
include "cr.mm"
include "cdvn.mm"
include "cdvds.mm"
include "etransclem16.mm"
include "nnzd.mm"
include "wcel.mm"
include "wa.mm"
include "cz.mm"
include "cn.mm"
include "adantr.mm"
include "cn0.mm"
include "wceq.mm"
include "cmap.mm"
include "crab.mm"
include "cmpt.mm"
include "etransclem11.mm"
include "3eqtri.mm"
include "simpr.mm"
include "eqid.mm"
include "etransclem28.mm"
include "wne.mm"
include "wb.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "faccld.mm"
include "nnne0d.mm"
include "elfzelzd.mm"
include "etransclem26.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "pm3.22.mm"
include "adantll.mm"
include "wn.mm"
include "ad3antrrr.mm"
include "pm2.65da.mm"
include "neqned.mm"
include "simplr.mm"
include "ad2antrr.mm"
include "etransclem24.mm"
include "mpdan.mm"
include "wf.mm"
include "etransclem12.mm"
include "eleqtrd.mm"
include "rabid.mm"
include "sylib.mm"
include "simpld.mm"
include "elmapi.mm"
include "simprd.mm"
include "w3a.mm"
include "cle.mm"
include "1zzd.mm"
include "nn0zd.mm"
include "3jca.mm"
include "elfznn0.mm"
include "neqne.mm"
include "anim12i.mm"
include "elnnne0.mm"
include "sylibr.mm"
include "nnge1d.mm"
include "elfzle2.mm"
include "jca32.mm"
include "elfz2.mm"
include "adantlr.mm"
include "etransclem25.mm"
include "caddc.mm"
include "nncnd.mm"
include "1cnd.mm"
include "npcand.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "facp1.mm"
include "oveq2d.mm"
include "mulcomd.mm"
include "eqtrd.mm"
include "3eqtrrd.mm"
include "zcnd.mm"
include "cc.mm"
include "divcan1d.mm"
include "3brtr4d.mm"
include "dvdsmulcr.mm"
include "syl112anc.mm"
include "pm2.61dan.mm"
include "fsumdvds.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "a1i.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "reopn.mm"
include "tgioo2.mm"
include "eleqtri.mm"
include "etransclem5.mm"
include "fzssre.mm"
include "sseldi.mm"
include "etransclem31.mm"
include "oveq1d.mm"
include "fsumdivc.mm"
include "breqtrrd.mm"

theorem etransclem38
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cP: class P
  let vj: setvar j
  let vn: setvar n
  let cF: class F
  let cI: class I
  let cJ: class J
  let cM: class M
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vk: setvar k
  let vm: setvar m
  let vy: setvar y
  assume etransclem38.p: |- ( ph -> P e. NN )
  assume etransclem38.m: |- ( ph -> M e. NN0 )
  assume etransclem38.f: |- F = ( x e. RR |-> ( ( x ^ ( P - 1 ) ) x. prod_ j e. ( 1 ... M ) ( ( x - j ) ^ P ) ) )
  assume etransclem38.i: |- ( ph -> I e. NN0 )
  assume etransclem38.j: |- ( ph -> J e. ( 0 ... M ) )
  assume etransclem38.ij: |- ( ph -> -. ( I = ( P - 1 ) /\ J = 0 ) )
  assume etransclem38.c: |- C = ( n e. NN0 |-> { c e. ( ( 0 ... n ) ^m ( 0 ... M ) ) | sum_ j e. ( 0 ... M ) ( c ` j ) = n } )

  disjoint C c
  disjoint C j
  disjoint C n
  disjoint C x
  disjoint c j
  disjoint c n
  disjoint c x
  disjoint j n
  disjoint j x
  disjoint n x
  disjoint I c
  disjoint I j
  disjoint I n
  disjoint I x
  disjoint J c
  disjoint J j
  disjoint J n
  disjoint J x
  disjoint M c
  disjoint M j
  disjoint M n
  disjoint M x
  disjoint P c
  disjoint P j
  disjoint P n
  disjoint P x
  disjoint c ph
  disjoint j ph
  disjoint n ph
  disjoint ph x
  disjoint I d
  disjoint c d
  disjoint d j
  disjoint d n
  disjoint M d
  disjoint M e
  disjoint M k
  disjoint c e
  disjoint c k
  disjoint d e
  disjoint d k
  disjoint e j
  disjoint e k
  disjoint e n
  disjoint j k
  disjoint k n
  disjoint M m
  disjoint c m
  disjoint d m
  disjoint e m
  disjoint j m
  disjoint m n
  disjoint k x
  disjoint P k
  disjoint P y
  disjoint c y
  disjoint j y
  disjoint k y
  disjoint n y
  disjoint x y
  disjoint k x
  assert |- ( ph -> P || ( ( ( ( RR Dn F ) ` I ) ` J ) / ( ! ` ( P - 1 ) ) ) )

  proof
    wph
    cP
    cI
    cC
    cfv
    #
    cI
    cfa
    cfv
    cc0
    cM
    cfz
    co
    #
    vj
    cv
    #
    vc
    cv
    #
    cfv
    #
    cfa
    cfv
    vj
    cprod
    cdiv
    co
    cP
    c1
    cmin
    co
    #
    cc0
    @3
    cfv
    #
    clt
    wbr
    cc0
    @5
    cfa
    cfv
    #
    @5
    @6
    cmin
    co
    #
    cfa
    cfv
    cdiv
    co
    cJ
    @8
    cexp
    co
    cmul
    co
    cif
    c1
    cM
    cfz
    co
    #
    cP
    @4
    clt
    wbr
    cc0
    cP
    cfa
    cfv
    #
    cP
    @4
    cmin
    co
    #
    cfa
    cfv
    cdiv
    co
    cJ
    @2
    cmin
    co
    @11
    cexp
    co
    cmul
    co
    cif
    vj
    cprod
    cmul
    co
    cmul
    co
    #
    @7
    cdiv
    co
    #
    vc
    csu
    #
    cJ
    cI
    cr
    cF
    cdvn
    co
    cfv
    cfv
    #
    @7
    cdiv
    co
    #
    cdvds
    wph
    @0
    @13
    vc
    cP
    wph
    cC
    vj
    vn
    cM
    cI
    vc
    etransclem38.c
    etransclem38.i
    etransclem16
    #
    wph
    cP
    etransclem38.p
    nnzd
    #
    wph
    @3
    @0
    wcel
    #
    wa
    #
    @7
    @12
    cdvds
    wbr
    #
    @13
    cz
    wcel
    #
    @20
    cC
    @3
    cP
    @12
    vj
    vn
    cJ
    cM
    cI
    vd
    wph
    cP
    cn
    wcel
    #
    @19
    etransclem38.p
    adantr
    #
    wph
    cM
    cn0
    wcel
    #
    @19
    etransclem38.m
    adantr
    #
    wph
    cI
    cn0
    wcel
    #
    @19
    etransclem38.i
    adantr
    #
    cC
    vn
    cn0
    @1
    @4
    vj
    csu
    #
    vn
    cv
    #
    wceq
    vc
    cc0
    @30
    cfz
    co
    @1
    cmap
    co
    #
    crab
    cmpt
    vm
    cn0
    @1
    vk
    cv
    #
    ve
    cv
    cfv
    vk
    csu
    vm
    cv
    #
    wceq
    ve
    cc0
    @33
    cfz
    co
    @1
    cmap
    co
    crab
    cmpt
    vn
    cn0
    @1
    @2
    vd
    cv
    cfv
    vj
    csu
    @30
    wceq
    vd
    @31
    crab
    cmpt
    etransclem38.c
    vj
    vk
    vm
    vn
    cM
    vc
    ve
    etransclem11
    vk
    vj
    vn
    vm
    cM
    ve
    vd
    etransclem11
    3eqtri
    #
    wph
    @19
    simpr
    #
    wph
    cJ
    @1
    wcel
    #
    @19
    etransclem38.j
    adantr
    @12
    eqid
    #
    etransclem28
    @20
    @7
    cz
    wcel
    #
    @7
    cc0
    wne
    #
    @12
    cz
    wcel
    @21
    @22
    wb
    wph
    @38
    @19
    wph
    @7
    wph
    @5
    wph
    @23
    @5
    cn0
    wcel
    #
    etransclem38.p
    cP
    nnm1nn0
    syl
    #
    faccld
    #
    nnzd
    #
    adantr
    wph
    @39
    @19
    wph
    @7
    @42
    nnne0d
    #
    adantr
    #
    @20
    cC
    @3
    cP
    vj
    vn
    cJ
    cM
    cI
    vd
    @24
    @26
    @28
    wph
    cJ
    cz
    wcel
    #
    @19
    wph
    cJ
    cc0
    cM
    etransclem38.j
    elfzelzd
    #
    adantr
    @34
    @35
    etransclem26
    #
    @7
    @12
    dvdsval2
    syl3anc
    mpbid
    #
    @20
    cJ
    cc0
    wceq
    #
    cP
    @13
    cdvds
    wbr
    #
    @20
    @50
    wa
    #
    cI
    @5
    wne
    #
    @51
    @52
    cI
    @5
    @52
    cI
    @5
    wceq
    #
    @54
    @50
    wa
    #
    @50
    @54
    @55
    @20
    @50
    @54
    pm3.22
    adantll
    wph
    @55
    wn
    @19
    @50
    @54
    etransclem38.ij
    ad3antrrr
    pm2.65da
    neqned
    @52
    @53
    wa
    cC
    @3
    cP
    vj
    vn
    cI
    cJ
    cM
    vd
    wph
    @23
    @19
    @50
    @53
    etransclem38.p
    ad3antrrr
    wph
    @25
    @19
    @50
    @53
    etransclem38.m
    ad3antrrr
    wph
    @27
    @19
    @50
    @53
    etransclem38.i
    ad3antrrr
    @52
    @53
    simpr
    @20
    @50
    @53
    simplr
    @34
    @20
    @19
    @50
    @53
    @35
    ad2antrr
    etransclem24
    mpdan
    @20
    @50
    wn
    #
    wa
    #
    cP
    @7
    cmul
    co
    #
    @13
    @7
    cmul
    co
    #
    cdvds
    wbr
    #
    @51
    @57
    @10
    @12
    @58
    @59
    cdvds
    @57
    @3
    cP
    @12
    vj
    cJ
    cM
    cI
    wph
    @23
    @19
    @56
    etransclem38.p
    ad2antrr
    wph
    @25
    @19
    @56
    etransclem38.m
    ad2antrr
    wph
    @27
    @19
    @56
    etransclem38.i
    ad2antrr
    @20
    @1
    cc0
    cI
    cfz
    co
    #
    @3
    wf
    #
    @56
    @20
    @3
    @61
    @1
    cmap
    co
    #
    wcel
    #
    @62
    @20
    @64
    @29
    cI
    wceq
    #
    @20
    @3
    @65
    vc
    @63
    crab
    #
    wcel
    @64
    @65
    wa
    @20
    @3
    @0
    @66
    @35
    wph
    @0
    @66
    wceq
    @19
    wph
    cC
    vj
    vn
    cM
    cI
    vc
    etransclem38.c
    etransclem38.i
    etransclem12
    adantr
    eleqtrd
    @65
    vc
    @63
    rabid
    sylib
    #
    simpld
    @3
    @61
    @1
    elmapi
    syl
    adantr
    @20
    @65
    @56
    @20
    @64
    @65
    @67
    simprd
    adantr
    @37
    wph
    @56
    cJ
    @9
    wcel
    #
    @19
    wph
    @56
    wa
    #
    c1
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    @46
    w3a
    #
    c1
    cJ
    cle
    wbr
    #
    cJ
    cM
    cle
    wbr
    #
    wa
    wa
    @68
    @69
    @72
    @73
    @74
    @69
    @70
    @71
    @46
    @69
    1zzd
    wph
    @71
    @56
    wph
    cM
    etransclem38.m
    nn0zd
    adantr
    wph
    @46
    @56
    @47
    adantr
    3jca
    @69
    cJ
    @69
    cJ
    cn0
    wcel
    #
    cJ
    cc0
    wne
    #
    wa
    cJ
    cn
    wcel
    wph
    @75
    @56
    @76
    wph
    @36
    @75
    etransclem38.j
    cJ
    cM
    elfznn0
    syl
    cJ
    cc0
    neqne
    anim12i
    cJ
    elnnne0
    sylibr
    nnge1d
    wph
    @74
    @56
    wph
    @36
    @74
    etransclem38.j
    cJ
    cc0
    cM
    elfzle2
    syl
    adantr
    jca32
    cJ
    c1
    cM
    elfz2
    sylibr
    adantlr
    etransclem25
    wph
    @58
    @10
    wceq
    @19
    @56
    wph
    @10
    @5
    c1
    caddc
    co
    #
    cfa
    cfv
    #
    @7
    @77
    cmul
    co
    #
    @58
    wph
    cP
    @77
    cfa
    wph
    @77
    cP
    wph
    cP
    c1
    wph
    cP
    etransclem38.p
    nncnd
    #
    wph
    1cnd
    npcand
    #
    eqcomd
    fveq2d
    wph
    @40
    @78
    @79
    wceq
    @41
    @5
    facp1
    syl
    wph
    @79
    @7
    cP
    cmul
    co
    @58
    wph
    @77
    cP
    @7
    cmul
    @81
    oveq2d
    wph
    @7
    cP
    wph
    @7
    @42
    nncnd
    #
    @80
    mulcomd
    eqtrd
    3eqtrrd
    ad2antrr
    @20
    @59
    @12
    wceq
    @56
    @20
    @12
    @7
    @20
    @12
    @48
    zcnd
    #
    wph
    @7
    cc
    wcel
    @19
    @82
    adantr
    @45
    divcan1d
    adantr
    3brtr4d
    @57
    cP
    cz
    wcel
    #
    @22
    @38
    @39
    @60
    @51
    wb
    wph
    @84
    @19
    @56
    @18
    ad2antrr
    @20
    @22
    @56
    @49
    adantr
    wph
    @38
    @19
    @56
    @43
    ad2antrr
    wph
    @39
    @19
    @56
    @44
    ad2antrr
    @7
    cP
    @13
    dvdsmulcr
    syl112anc
    mpbid
    pm2.61dan
    fsumdvds
    wph
    @16
    @0
    @12
    vc
    csu
    #
    @7
    cdiv
    co
    @14
    wph
    @15
    @85
    @7
    cdiv
    wph
    vx
    cC
    cP
    cr
    vj
    vn
    cF
    vk
    @1
    vy
    cr
    vy
    cv
    @32
    cmin
    co
    @32
    cc0
    wceq
    @5
    cP
    cif
    cexp
    co
    cmpt
    cmpt
    cM
    cI
    cr
    cJ
    vc
    cr
    cr
    cc
    cpr
    wcel
    wph
    reelprrecn
    a1i
    cr
    ccnfld
    ctopn
    cfv
    #
    cr
    crest
    co
    #
    wcel
    wph
    cr
    cioo
    crn
    ctg
    cfv
    @87
    reopn
    @86
    @86
    eqid
    tgioo2
    eleqtri
    a1i
    etransclem38.p
    etransclem38.m
    etransclem38.f
    etransclem38.i
    vy
    vx
    cP
    vk
    vj
    cM
    cr
    etransclem5
    etransclem38.c
    wph
    @1
    cr
    cJ
    cc0
    cM
    fzssre
    etransclem38.j
    sseldi
    etransclem31
    oveq1d
    wph
    @0
    @12
    @7
    vc
    @17
    @82
    @83
    @44
    fsumdivc
    eqtrd
    breqtrrd
end
