include "caddc.mm"
include "cseq.mm"
include "cfv.mm"
include "c1.mm"
include "cli.mm"
include "cuz.mm"
include "cfz.mm"
include "co.mm"
include "wf1o.mm"
include "wf.mm"
include "clt.mm"
include "wiso.mm"
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
include "cn.mm"
include "cn0.mm"
include "nnnn0.mm"
include "hashfz1.mm"
include "3syl.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "isoeq4.mm"
include "mpbid.mm"
include "isof1o.mm"
include "f1of.mm"
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
include "fsumcvg.mm"
include "cc.mm"
include "cc0.mm"
include "addid2.mm"
include "adantl.mm"
include "addid1.mm"
include "addcl.mm"
include "0cnd.mm"
include "eleqtrrd.mm"
include "cif.mm"
include "iftrue.mm"
include "eqeltrd.mm"
include "wn.mm"
include "iffalse.mm"
include "0cn.mm"
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
include "summolem3.mm"
include "eqtr4d.mm"
include "breqtrd.mm"

theorem summolem2a
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cM: class M
  let cN: class N
  let vg: setvar g
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  assume summo.1: |- F = ( k e. ZZ |-> if ( k e. A , B , 0 ) )
  assume summo.2: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume summo.3: |- G = ( n e. NN |-> [_ ( f ` n ) / k ]_ B )
  assume summolem2.4: |- H = ( n e. NN |-> [_ ( K ` n ) / k ]_ B )
  assume summolem2.5: |- ( ph -> N e. NN )
  assume summolem2.6: |- ( ph -> M e. ZZ )
  assume summolem2.7: |- ( ph -> A C_ ( ZZ>= ` M ) )
  assume summolem2.8: |- ( ph -> f : ( 1 ... N ) -1-1-onto-> A )
  assume summolem2.9: |- ( ph -> K Isom < , < ( ( 1 ... ( # ` A ) ) , A ) )

  disjoint f k
  disjoint f n
  disjoint A f
  disjoint k n
  disjoint A k
  disjoint A n
  disjoint F f
  disjoint F k
  disjoint F n
  disjoint G k
  disjoint G n
  disjoint K k
  disjoint K n
  disjoint N k
  disjoint N n
  disjoint k ph
  disjoint n ph
  disjoint B f
  disjoint B n
  disjoint M k
  disjoint M n
  disjoint f g
  disjoint f i
  disjoint f j
  disjoint f m
  disjoint f x
  disjoint f y
  disjoint g i
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint A i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint A j
  disjoint k m
  disjoint k x
  disjoint k y
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F g
  disjoint F j
  disjoint F m
  disjoint F x
  disjoint F y
  disjoint G g
  disjoint G i
  disjoint G j
  disjoint G m
  disjoint G x
  disjoint G y
  disjoint H i
  disjoint H x
  disjoint K i
  disjoint K j
  disjoint K m
  disjoint K x
  disjoint K y
  disjoint N m
  disjoint g ph
  disjoint i ph
  disjoint j ph
  disjoint m ph
  disjoint ph y
  disjoint B j
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint M i
  disjoint M j
  disjoint M m
  disjoint M x
  disjoint M y
  disjoint ph x
  assert |- ( ph -> seq M ( + , F ) ~~> ( seq 1 ( + , G ) ` N ) )

  proof
    wph
    caddc
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
    caddc
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
    summo.1
    summo.2
    wph
    cA
    cM
    cuz
    cfv
    #
    @1
    summolem2.7
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
    cK
    wf1o
    #
    @5
    cA
    cK
    wf
    wph
    @5
    cA
    clt
    clt
    cK
    wiso
    #
    @6
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
    @7
    summolem2.9
    wph
    @9
    @5
    wceq
    @10
    @7
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
    summolem2.8
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
    cn
    wcel
    #
    cN
    cn0
    wcel
    @11
    cN
    wceq
    summolem2.5
    cN
    nnnn0
    cN
    hashfz1
    3syl
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
    syl
    #
    @5
    cA
    cK
    f1of
    syl
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
    @23
    summolem2.5
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
    vn
    cA
    cM
    @1
    cfz
    co
    #
    wph
    vn
    cv
    #
    cA
    wcel
    #
    @28
    @27
    wcel
    #
    wph
    @29
    wa
    #
    @28
    @4
    wcel
    #
    @1
    @28
    cuz
    cfv
    wcel
    #
    @30
    wph
    cA
    @4
    @28
    summolem2.7
    sselda
    #
    @31
    @33
    @28
    @1
    cle
    wbr
    #
    @31
    @28
    cK
    ccnv
    #
    cfv
    #
    cK
    cfv
    #
    @28
    @1
    cle
    wph
    @6
    @29
    @38
    @28
    wceq
    @22
    @5
    cA
    @28
    cK
    f1ocnvfv2
    sylan
    @31
    @37
    cN
    cle
    wbr
    #
    @38
    @1
    cle
    wbr
    #
    @31
    @37
    @5
    wcel
    #
    @39
    wph
    cA
    @5
    @28
    @36
    wph
    @6
    cA
    @5
    @36
    wf1o
    cA
    @5
    @36
    wf
    @22
    @5
    cA
    cK
    f1ocnv
    cA
    @5
    @36
    f1of
    3syl
    ffvelrnda
    #
    @37
    c1
    cN
    elfzle2
    syl
    @31
    @7
    @5
    cxr
    wss
    #
    cA
    cxr
    wss
    @41
    @24
    @39
    @40
    wb
    wph
    @7
    @29
    @21
    adantr
    @43
    @31
    @5
    cr
    cxr
    @5
    @23
    cr
    c1
    cN
    fzssuz
    @23
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
    @31
    cA
    cr
    cxr
    @31
    cA
    @4
    cr
    wph
    cA
    @4
    wss
    #
    @29
    summolem2.7
    adantr
    @4
    cz
    cr
    cM
    uzssz
    zssre
    sstri
    syl6ss
    ressxr
    syl6ss
    @42
    wph
    @24
    @29
    @25
    adantr
    @5
    cA
    @37
    cN
    cK
    leisorel
    syl122anc
    mpbid
    eqbrtrrd
    @31
    @28
    cz
    wcel
    #
    @1
    cz
    wcel
    #
    @33
    @35
    wb
    @31
    @32
    @45
    @34
    cM
    @28
    eluzelz
    syl
    wph
    @46
    @29
    wph
    @1
    @4
    wcel
    @46
    @26
    cM
    @1
    eluzelz
    syl
    adantr
    @28
    @1
    eluz
    syl2anc
    mpbird
    @28
    cM
    @1
    elfzuzb
    sylanbrc
    ex
    ssrdv
    fsumcvg
    wph
    @2
    cN
    caddc
    cH
    c1
    cseq
    cfv
    @3
    wph
    cA
    caddc
    cc
    vm
    vx
    cF
    cK
    cH
    cM
    cN
    cc0
    vm
    cv
    #
    cc
    wcel
    #
    cc0
    @47
    caddc
    co
    @47
    wceq
    wph
    @47
    addid2
    adantl
    @48
    @47
    cc0
    caddc
    co
    @47
    wceq
    wph
    @47
    addid1
    adantl
    @48
    vx
    cv
    #
    cc
    wcel
    wa
    @47
    @49
    caddc
    co
    cc
    wcel
    wph
    @47
    @49
    addcl
    adantl
    wph
    0cnd
    summolem2.9
    wph
    cN
    @5
    @9
    @25
    @20
    eleqtrrd
    summolem2.7
    wph
    cz
    cc
    cF
    wf
    @47
    cz
    wcel
    @47
    cF
    cfv
    #
    cc
    wcel
    @47
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
    cc0
    cif
    #
    cc
    cF
    wph
    @55
    cc
    wcel
    #
    @53
    cz
    wcel
    #
    wph
    @54
    @56
    wph
    @54
    @56
    wph
    @54
    wa
    @55
    cB
    cc
    @54
    @55
    cB
    wceq
    wph
    @54
    cB
    cc0
    iftrue
    adantl
    summo.2
    eqeltrd
    ex
    @54
    wn
    #
    @55
    cc0
    cc
    @54
    cB
    cc0
    iffalse
    #
    0cn
    syl6eqel
    pm2.61d1
    #
    adantr
    summo.1
    fmptd
    @47
    cM
    @51
    elfzelz
    cz
    cc
    @47
    cF
    ffvelrn
    syl2an
    @47
    @52
    cA
    cdif
    #
    wcel
    @50
    cc0
    wceq
    #
    wph
    @53
    cF
    cfv
    #
    cc0
    wceq
    @62
    vk
    @47
    @61
    vk
    vm
    weq
    @63
    @50
    cc0
    @53
    @47
    cF
    fveq2
    eqeq1d
    @53
    @61
    wcel
    #
    @63
    @55
    cc0
    @64
    @57
    @56
    @63
    @55
    wceq
    @64
    @53
    @52
    wcel
    @57
    @53
    @52
    cA
    eldifi
    @53
    cM
    @51
    elfzelz
    syl
    @64
    @55
    cc0
    cc
    @64
    @58
    @55
    cc0
    wceq
    @53
    @52
    cA
    eldifn
    @59
    syl
    #
    0cn
    syl6eqel
    vk
    cz
    @55
    cc
    cF
    summo.1
    fvmpt2
    syl2anc
    @65
    eqtrd
    vtoclga
    adantl
    wph
    @49
    @9
    wcel
    #
    wa
    #
    @49
    cK
    cfv
    #
    cA
    wcel
    #
    vk
    @68
    cB
    csb
    #
    cc0
    cif
    #
    @70
    @68
    cF
    cfv
    #
    @49
    cH
    cfv
    #
    @67
    @69
    @70
    cc0
    wph
    @9
    cA
    @49
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
    summolem2.9
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
    @67
    @68
    cz
    wcel
    #
    @71
    cc
    wcel
    #
    @72
    @71
    wceq
    @67
    @68
    @4
    wcel
    @76
    @67
    cA
    @4
    @68
    wph
    @44
    @66
    summolem2.7
    adantr
    @74
    sseldd
    cM
    @68
    eluzelz
    syl
    wph
    @77
    @66
    wph
    @56
    wi
    wph
    @77
    wi
    vk
    @68
    wph
    @77
    vk
    wph
    vk
    nfv
    vk
    @71
    cc
    @69
    vk
    @70
    cc0
    @69
    vk
    nfv
    vk
    @68
    cB
    nfcsb1v
    vk
    cc0
    nfcv
    #
    nfif
    nfel1
    nfim
    @49
    cK
    fvex
    @53
    @68
    wceq
    #
    @56
    @77
    wph
    @79
    @55
    @71
    cc
    @79
    @54
    @69
    cB
    @70
    cc0
    @53
    @68
    cA
    eleq1
    vk
    @68
    cB
    csbeq1a
    ifbieq1d
    eleq1d
    imbi2d
    @60
    vtoclf
    adantr
    #
    vn
    @68
    @29
    vk
    @28
    cB
    csb
    #
    cc0
    cif
    #
    @71
    cz
    cc
    cF
    @28
    @68
    wceq
    @29
    @69
    @81
    @70
    cc0
    @28
    @68
    cA
    eleq1
    vk
    @28
    @68
    cB
    csbeq1
    ifbieq1d
    cF
    vk
    cz
    @55
    cmpt
    vn
    cz
    @82
    cmpt
    summo.1
    vk
    vn
    cz
    @55
    @82
    vn
    @55
    nfcv
    @29
    vk
    @81
    cc0
    @29
    vk
    nfv
    vk
    @28
    cB
    nfcsb1v
    @78
    nfif
    vk
    vn
    weq
    @54
    @29
    cB
    @81
    cc0
    @53
    @28
    cA
    eleq1
    vk
    @28
    cB
    csbeq1a
    ifbieq1d
    cbvmpt
    eqtri
    fvmptg
    syl2anc
    @67
    @49
    cn
    wcel
    #
    @70
    cc
    wcel
    @73
    @70
    wceq
    @66
    @83
    wph
    @49
    @8
    elfznn
    adantl
    @67
    @71
    @70
    cc
    @75
    @80
    eqeltrrd
    vn
    @49
    vk
    @28
    cK
    cfv
    #
    cB
    csb
    @70
    cn
    cc
    cH
    vn
    vx
    weq
    vk
    @84
    @68
    cB
    @28
    @49
    cK
    fveq2
    csbeq1d
    summolem2.4
    fvmptg
    syl2anc
    3eqtr4rd
    seqcoll
    wph
    cA
    cB
    vf
    vk
    vn
    cF
    cG
    cH
    cK
    cN
    cN
    summo.1
    summo.2
    summo.3
    summolem2.4
    wph
    @19
    @19
    summolem2.5
    summolem2.5
    jca
    summolem2.8
    @22
    summolem3
    eqtr4d
    breqtrd
end
