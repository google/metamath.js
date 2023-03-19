include "cmul.mm"
include "cseq.mm"
include "cfv.mm"
include "c1.mm"
include "cli.mm"
include "cuz.mm"
include "cfz.mm"
include "co.mm"
include "clt.mm"
include "wiso.mm"
include "wf1o.mm"
include "wf.mm"
include "chash.mm"
include "wceq.mm"
include "wb.mm"
include "cen.mm"
include "wbr.mm"
include "cv.mm"
include "ovex.mm"
include "f1oen.mm"
include "syl.mm"
include "cfn.mm"
include "wcel.mm"
include "fzfid.mm"
include "ensymd.mm"
include "enfii.mm"
include "syl2anc.mm"
include "hashen.mm"
include "mpbird.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "hashfz1.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "isoeq4.mm"
include "mpbid.mm"
include "isof1o.mm"
include "f1of.mm"
include "3syl.mm"
include "cn.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "eluzfz2.mm"
include "ffvelrnd.mm"
include "sseldd.mm"
include "wa.mm"
include "sselda.mm"
include "cle.mm"
include "ccnv.mm"
include "f1ocnvfv2.mm"
include "sylan.mm"
include "f1ocnv.mm"
include "ffvelrnda.mm"
include "elfzle2.mm"
include "cxr.mm"
include "wss.mm"
include "adantr.mm"
include "cr.mm"
include "fzssuz.mm"
include "cz.mm"
include "uzssz.mm"
include "zssre.mm"
include "sstri.mm"
include "ressxr.mm"
include "a1i.mm"
include "syl6ss.mm"
include "leisorel.mm"
include "syl122anc.mm"
include "eqbrtrrd.mm"
include "eluzelz.mm"
include "eluz.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "ex.mm"
include "ssrdv.mm"
include "fprodcvg.mm"
include "cc.mm"
include "mulid2.mm"
include "adantl.mm"
include "mulid1.mm"
include "mulcl.mm"
include "1cnd.mm"
include "eleqtrrd.mm"
include "cif.mm"
include "iftrue.mm"
include "eqeltrd.mm"
include "wn.mm"
include "iffalse.mm"
include "ax-1cn.mm"
include "syl6eqel.mm"
include "pm2.61d1.mm"
include "fmptd.mm"
include "elfzelz.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "cdif.mm"
include "weq.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "eldifi.mm"
include "sseldi.mm"
include "eldifn.mm"
include "fvmpt2.mm"
include "eqtrd.mm"
include "vtoclga.mm"
include "csb.mm"
include "iftrued.mm"
include "wi.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfcv.mm"
include "nfif.mm"
include "nfel1.mm"
include "nfim.mm"
include "fvex.mm"
include "eleq1.mm"
include "csbeq1a.mm"
include "ifbieq1d.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "vtoclf.mm"
include "csbeq1.mm"
include "cmpt.mm"
include "cbvmpt.mm"
include "eqtri.mm"
include "fvmptg.mm"
include "elfznn.mm"
include "eqeltrrd.mm"
include "csbeq1d.mm"
include "3eqtr4rd.mm"
include "seqcoll.mm"
include "jca.mm"
include "prodmolem3.mm"
include "eqtr4d.mm"
include "breqtrd.mm"

theorem prodmolem2a
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vx: setvar x
  let vn: setvar n
  assume prodmo.1: |- F = ( k e. ZZ |-> if ( k e. A , B , 1 ) )
  assume prodmo.2: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume prodmo.3: |- G = ( j e. NN |-> [_ ( f ` j ) / k ]_ B )
  assume prodmolem2.4: |- H = ( j e. NN |-> [_ ( K ` j ) / k ]_ B )
  assume prodmolem2.5: |- ( ph -> N e. NN )
  assume prodmolem2.6: |- ( ph -> M e. ZZ )
  assume prodmolem2.7: |- ( ph -> A C_ ( ZZ>= ` M ) )
  assume prodmolem2.8: |- ( ph -> f : ( 1 ... N ) -1-1-onto-> A )
  assume prodmolem2.9: |- ( ph -> K Isom < , < ( ( 1 ... ( # ` A ) ) , A ) )

  disjoint A j
  disjoint B j
  disjoint f j
  disjoint f k
  disjoint G j
  disjoint j k
  disjoint j ph
  disjoint K j
  disjoint K k
  disjoint M j
  disjoint M k
  disjoint N j
  disjoint N k
  disjoint A k
  disjoint F k
  disjoint k ph
  disjoint A m
  disjoint A x
  disjoint B n
  disjoint F m
  disjoint F x
  disjoint H x
  disjoint j x
  disjoint k m
  disjoint K m
  disjoint K n
  disjoint k x
  disjoint K x
  disjoint M m
  disjoint m ph
  disjoint m x
  disjoint M x
  disjoint n x
  disjoint ph x
  disjoint A n
  disjoint k n
  disjoint F n
  disjoint n ph
  disjoint M n
  disjoint N n
  assert |- ( ph -> seq M ( x. , F ) ~~> ( seq 1 ( x. , G ) ` N ) )

  proof
    wph
    cmul
    cF
    cM
    cseq
    #
    cN
    cK
    cfv
    #
    @0
    cfv
    #
    cN
    cmul
    cG
    c1
    cseq
    cfv
    #
    cli
    wph
    cA
    cB
    vk
    cF
    cM
    @1
    prodmo.1
    prodmo.2
    wph
    cA
    cM
    cuz
    cfv
    #
    @1
    prodmolem2.7
    wph
    c1
    cN
    cfz
    co
    #
    cA
    cN
    cK
    wph
    @5
    cA
    clt
    clt
    cK
    wiso
    #
    @5
    cA
    cK
    wf1o
    #
    @5
    cA
    cK
    wf
    wph
    c1
    cA
    chash
    cfv
    #
    cfz
    co
    #
    cA
    clt
    clt
    cK
    wiso
    #
    @6
    prodmolem2.9
    wph
    @9
    @5
    wceq
    @10
    @6
    wb
    wph
    @8
    cN
    c1
    cfz
    wph
    @5
    chash
    cfv
    #
    @8
    cN
    wph
    @11
    @8
    wceq
    #
    @5
    cA
    cen
    wbr
    #
    wph
    @5
    cA
    vf
    cv
    #
    wf1o
    @13
    prodmolem2.8
    @5
    cA
    @14
    c1
    cN
    cfz
    ovex
    f1oen
    syl
    #
    wph
    @5
    cfn
    wcel
    #
    cA
    cfn
    wcel
    #
    @12
    @13
    wb
    wph
    c1
    cN
    fzfid
    #
    wph
    @16
    cA
    @5
    cen
    wbr
    @17
    @18
    wph
    @5
    cA
    @15
    ensymd
    cA
    @5
    enfii
    syl2anc
    @5
    cA
    hashen
    syl2anc
    mpbird
    wph
    cN
    cn0
    wcel
    @11
    cN
    wceq
    wph
    cN
    prodmolem2.5
    nnnn0d
    cN
    hashfz1
    syl
    eqtr3d
    oveq2d
    #
    @9
    cA
    @5
    clt
    clt
    cK
    isoeq4
    syl
    mpbid
    #
    @5
    cA
    clt
    clt
    cK
    isof1o
    #
    @5
    cA
    cK
    f1of
    3syl
    wph
    cN
    c1
    cuz
    cfv
    #
    wcel
    cN
    @5
    wcel
    #
    wph
    cN
    cn
    @22
    prodmolem2.5
    nnuz
    syl6eleq
    c1
    cN
    eluzfz2
    syl
    #
    ffvelrnd
    sseldd
    #
    wph
    vj
    cA
    cM
    @1
    cfz
    co
    #
    wph
    vj
    cv
    #
    cA
    wcel
    #
    @27
    @26
    wcel
    #
    wph
    @28
    wa
    #
    @27
    @4
    wcel
    @1
    @27
    cuz
    cfv
    wcel
    #
    @29
    wph
    cA
    @4
    @27
    prodmolem2.7
    sselda
    @30
    @31
    @27
    @1
    cle
    wbr
    #
    @30
    @27
    cK
    ccnv
    #
    cfv
    #
    cK
    cfv
    #
    @27
    @1
    cle
    wph
    @7
    @28
    @35
    @27
    wceq
    wph
    @6
    @7
    @20
    @21
    syl
    #
    @5
    cA
    @27
    cK
    f1ocnvfv2
    sylan
    @30
    @34
    cN
    cle
    wbr
    #
    @35
    @1
    cle
    wbr
    #
    @30
    @34
    @5
    wcel
    #
    @37
    wph
    cA
    @5
    @27
    @33
    wph
    @7
    cA
    @5
    @33
    wf1o
    cA
    @5
    @33
    wf
    @36
    @5
    cA
    cK
    f1ocnv
    cA
    @5
    @33
    f1of
    3syl
    ffvelrnda
    #
    @34
    c1
    cN
    elfzle2
    syl
    @30
    @6
    @5
    cxr
    wss
    #
    cA
    cxr
    wss
    #
    @39
    @23
    @37
    @38
    wb
    wph
    @6
    @28
    @20
    adantr
    @41
    @30
    @5
    cr
    cxr
    @5
    @22
    cr
    c1
    cN
    fzssuz
    @22
    cz
    cr
    c1
    uzssz
    zssre
    sstri
    sstri
    ressxr
    sstri
    a1i
    wph
    @42
    @28
    wph
    cA
    @4
    cxr
    prodmolem2.7
    @4
    cr
    cxr
    @4
    cz
    cr
    cM
    uzssz
    #
    zssre
    sstri
    ressxr
    sstri
    syl6ss
    adantr
    @40
    wph
    @23
    @28
    @24
    adantr
    @5
    cA
    @34
    cN
    cK
    leisorel
    syl122anc
    mpbid
    eqbrtrrd
    @30
    @27
    cz
    wcel
    @1
    cz
    wcel
    #
    @31
    @32
    wb
    wph
    cA
    cz
    @27
    wph
    cA
    @4
    cz
    prodmolem2.7
    @43
    syl6ss
    #
    sselda
    wph
    @44
    @28
    wph
    @1
    @4
    wcel
    @44
    @25
    cM
    @1
    eluzelz
    syl
    adantr
    @27
    @1
    eluz
    syl2anc
    mpbird
    @27
    cM
    @1
    elfzuzb
    sylanbrc
    ex
    ssrdv
    fprodcvg
    wph
    @2
    cN
    cmul
    cH
    c1
    cseq
    cfv
    @3
    wph
    cA
    cmul
    cc
    vm
    vx
    cF
    cK
    cH
    cM
    cN
    c1
    vm
    cv
    #
    cc
    wcel
    #
    c1
    @46
    cmul
    co
    @46
    wceq
    wph
    @46
    mulid2
    adantl
    @47
    @46
    c1
    cmul
    co
    @46
    wceq
    wph
    @46
    mulid1
    adantl
    @47
    vx
    cv
    #
    cc
    wcel
    wa
    @46
    @48
    cmul
    co
    cc
    wcel
    wph
    @46
    @48
    mulcl
    adantl
    wph
    1cnd
    prodmolem2.9
    wph
    cN
    @5
    @9
    @24
    @19
    eleqtrrd
    prodmolem2.7
    wph
    cz
    cc
    cF
    wf
    @46
    cz
    wcel
    @46
    cF
    cfv
    #
    cc
    wcel
    @46
    cM
    @8
    cK
    cfv
    #
    cfz
    co
    #
    wcel
    wph
    vk
    cz
    vk
    cv
    #
    cA
    wcel
    #
    cB
    c1
    cif
    #
    cc
    cF
    wph
    @54
    cc
    wcel
    #
    @52
    cz
    wcel
    #
    wph
    @53
    @55
    wph
    @53
    @55
    wph
    @53
    wa
    @54
    cB
    cc
    @53
    @54
    cB
    wceq
    wph
    @53
    cB
    c1
    iftrue
    adantl
    prodmo.2
    eqeltrd
    ex
    @53
    wn
    #
    @54
    c1
    cc
    @53
    cB
    c1
    iffalse
    #
    ax-1cn
    syl6eqel
    pm2.61d1
    #
    adantr
    prodmo.1
    fmptd
    @46
    cM
    @50
    elfzelz
    cz
    cc
    @46
    cF
    ffvelrn
    syl2an
    @46
    @51
    cA
    cdif
    #
    wcel
    @49
    c1
    wceq
    #
    wph
    @52
    cF
    cfv
    #
    c1
    wceq
    @61
    vk
    @46
    @60
    vk
    vm
    weq
    @62
    @49
    c1
    @52
    @46
    cF
    fveq2
    eqeq1d
    @52
    @60
    wcel
    #
    @62
    @54
    c1
    @63
    @56
    @55
    @62
    @54
    wceq
    @63
    @51
    cz
    @52
    @51
    @4
    cz
    cM
    @50
    fzssuz
    @43
    sstri
    @52
    @51
    cA
    eldifi
    sseldi
    @63
    @54
    c1
    cc
    @63
    @57
    @54
    c1
    wceq
    @52
    @51
    cA
    eldifn
    @58
    syl
    #
    ax-1cn
    syl6eqel
    vk
    cz
    @54
    cc
    cF
    prodmo.1
    fvmpt2
    syl2anc
    @64
    eqtrd
    vtoclga
    adantl
    wph
    @48
    @9
    wcel
    #
    wa
    #
    @48
    cK
    cfv
    #
    cA
    wcel
    #
    vk
    @67
    cB
    csb
    #
    c1
    cif
    #
    @69
    @67
    cF
    cfv
    #
    @48
    cH
    cfv
    #
    @66
    @68
    @69
    c1
    wph
    @9
    cA
    @48
    cK
    wph
    @10
    @9
    cA
    cK
    wf1o
    @9
    cA
    cK
    wf
    prodmolem2.9
    @9
    cA
    clt
    clt
    cK
    isof1o
    @9
    cA
    cK
    f1of
    3syl
    ffvelrnda
    #
    iftrued
    #
    @66
    @67
    cz
    wcel
    @70
    cc
    wcel
    #
    @71
    @70
    wceq
    @66
    cA
    cz
    @67
    wph
    cA
    cz
    wss
    @65
    @45
    adantr
    @73
    sseldd
    wph
    @75
    @65
    wph
    @55
    wi
    wph
    @75
    wi
    vk
    @67
    wph
    @75
    vk
    wph
    vk
    nfv
    vk
    @70
    cc
    @68
    vk
    @69
    c1
    @68
    vk
    nfv
    vk
    @67
    cB
    nfcsb1v
    vk
    c1
    nfcv
    #
    nfif
    nfel1
    nfim
    @48
    cK
    fvex
    @52
    @67
    wceq
    #
    @55
    @75
    wph
    @77
    @54
    @70
    cc
    @77
    @53
    @68
    cB
    @69
    c1
    @52
    @67
    cA
    eleq1
    vk
    @67
    cB
    csbeq1a
    ifbieq1d
    eleq1d
    imbi2d
    @59
    vtoclf
    adantr
    #
    vn
    @67
    vn
    cv
    #
    cA
    wcel
    #
    vk
    @79
    cB
    csb
    #
    c1
    cif
    #
    @70
    cz
    cc
    cF
    @79
    @67
    wceq
    @80
    @68
    @81
    @69
    c1
    @79
    @67
    cA
    eleq1
    vk
    @79
    @67
    cB
    csbeq1
    ifbieq1d
    cF
    vk
    cz
    @54
    cmpt
    vn
    cz
    @82
    cmpt
    prodmo.1
    vk
    vn
    cz
    @54
    @82
    vn
    @54
    nfcv
    @80
    vk
    @81
    c1
    @80
    vk
    nfv
    vk
    @79
    cB
    nfcsb1v
    @76
    nfif
    vk
    vn
    weq
    @53
    @80
    cB
    @81
    c1
    @52
    @79
    cA
    eleq1
    vk
    @79
    cB
    csbeq1a
    ifbieq1d
    cbvmpt
    eqtri
    fvmptg
    syl2anc
    @66
    @48
    cn
    wcel
    #
    @69
    cc
    wcel
    @72
    @69
    wceq
    @65
    @83
    wph
    @48
    @8
    elfznn
    adantl
    @66
    @70
    @69
    cc
    @74
    @78
    eqeltrrd
    vj
    @48
    vk
    @27
    cK
    cfv
    #
    cB
    csb
    @69
    cn
    cc
    cH
    vj
    vx
    weq
    vk
    @84
    @67
    cB
    @27
    @48
    cK
    fveq2
    csbeq1d
    prodmolem2.4
    fvmptg
    syl2anc
    3eqtr4rd
    seqcoll
    wph
    cA
    cB
    vf
    vj
    vk
    cF
    cG
    cH
    cK
    cN
    cN
    prodmo.1
    prodmo.2
    prodmo.3
    prodmolem2.4
    wph
    cN
    cn
    wcel
    #
    @85
    prodmolem2.5
    prodmolem2.5
    jca
    prodmolem2.8
    @36
    prodmolem3
    eqtr4d
    breqtrd
end
