include "cn0.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "cin.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "cuz.mm"
include "wa.mm"
include "cfz.mm"
include "cdif.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "eulerpartlemsf.mm"
include "ffvelrni.mm"
include "nndiffz1.mm"
include "eleq2d.mm"
include "syl.mm"
include "pm5.32i.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "simpr.mm"
include "eldif.mm"
include "sylib.mm"
include "simpld.mm"
include "wf.mm"
include "ccnv.mm"
include "cima.mm"
include "cfn.mm"
include "eulerpartlemelr.mm"
include "ffvelrnda.mm"
include "syldan.mm"
include "simpl.mm"
include "adantr.mm"
include "simprd.mm"
include "cle.mm"
include "cz.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "nn0zd.mm"
include "elfz5.mm"
include "syl2anc.mm"
include "notbid.mm"
include "nn0red.mm"
include "nnred.mm"
include "ltnled.mm"
include "bitr4d.mm"
include "biimpa.mm"
include "syl21anc.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "cmul.mm"
include "csu.mm"
include "eulerpartlemsv1.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "cbvsumv.mm"
include "syl6req.mm"
include "wne.mm"
include "breq2.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "cbvrexv.mm"
include "ad2antrr.mm"
include "cr.mm"
include "cmpt.mm"
include "1zzd.mm"
include "eqidd.mm"
include "fveq2d.mm"
include "ffvelrn.mm"
include "nnnn0d.mm"
include "nn0mulcld.mm"
include "fvmptd.mm"
include "cc.mm"
include "wss.mm"
include "cbvmptv.mm"
include "fmptd.mm"
include "nn0sscn.mm"
include "fss.mm"
include "sylancl.mm"
include "csupp.mm"
include "csn.mm"
include "cvv.mm"
include "nnex.mm"
include "0nn0.mm"
include "eqid.mm"
include "ffs2.mm"
include "mp3an12.mm"
include "frnnn0supp.mm"
include "sylancr.mm"
include "eqeltrd.mm"
include "a1i.mm"
include "ffn.mm"
include "w3a.mm"
include "simp3.mm"
include "oveq1d.mm"
include "simp2.mm"
include "nncnd.mm"
include "mul02d.mm"
include "eqtrd.mm"
include "suppss3.mm"
include "ssfi.mm"
include "eqeltrrd.mm"
include "fsumcvg4.mm"
include "isumrecl.mm"
include "simprl.mm"
include "remulcld.mm"
include "nn0ge0d.mm"
include "simprr.mm"
include "elnnnn0b.mm"
include "nnge1.mm"
include "sylbir.mm"
include "lemulge12d.mm"
include "nn0cnd.mm"
include "mulcld.mm"
include "sumsn.mm"
include "snfi.mm"
include "snssd.mm"
include "isumless.mm"
include "eqbrtrrd.mm"
include "letrd.mm"
include "ltletrd.mm"
include "r19.29an.mm"
include "gtned.mm"
include "ex.mm"
include "syl5bi.mm"
include "necon2bd.mm"
include "mpd.mm"
include "ralnex.mm"
include "sylibr.mm"
include "imnan.mm"
include "ralbii.mm"
include "r19.21bi.mm"
include "imp.mm"
include "nn0re.mm"
include "0red.mm"
include "lenltd.mm"
include "nn0le0eq0.mm"
include "bitr3d.mm"

theorem eulerpartlems
  let vt: setvar t
  let cA: class A
  let cR: class R
  let cS: class S
  let vf: setvar f
  let vk: setvar k
  let vg: setvar g
  let vl: setvar l
  let vm: setvar m
  assume eulerpartlems.r: |- R = { f | ( `' f " NN ) e. Fin }
  assume eulerpartlems.s: |- S = ( f e. ( ( NN0 ^m NN ) i^i R ) |-> sum_ k e. NN ( ( f ` k ) x. k ) )

  disjoint f k
  disjoint A f
  disjoint A k
  disjoint R f
  disjoint R k
  disjoint k t
  disjoint A t
  disjoint R t
  disjoint S t
  disjoint f g
  disjoint g k
  disjoint R g
  disjoint k l
  disjoint k m
  disjoint l m
  disjoint l t
  disjoint A l
  disjoint m t
  disjoint A m
  disjoint R l
  disjoint S l
  assert |- ( ( A e. ( ( NN0 ^m NN ) i^i R ) /\ t e. ( ZZ>= ` ( ( S ` A ) + 1 ) ) ) -> ( A ` t ) = 0 )

  proof
    cA
    cn0
    cn
    cmap
    co
    cR
    cin
    #
    wcel
    #
    vt
    cv
    #
    cA
    cS
    cfv
    #
    c1
    caddc
    co
    cuz
    cfv
    #
    wcel
    #
    wa
    @1
    @2
    cn
    c1
    @3
    cfz
    co
    #
    cdif
    #
    wcel
    #
    wa
    #
    @2
    cA
    cfv
    #
    cc0
    wceq
    #
    @1
    @8
    @5
    @1
    @3
    cn0
    wcel
    #
    @8
    @5
    wb
    @0
    cn0
    cA
    cS
    cR
    cS
    vf
    vk
    eulerpartlems.r
    eulerpartlems.s
    eulerpartlemsf
    ffvelrni
    #
    @12
    @7
    @4
    @2
    @3
    nndiffz1
    eleq2d
    syl
    pm5.32i
    @9
    @10
    cn0
    wcel
    #
    cc0
    @10
    clt
    wbr
    #
    wn
    #
    @11
    @1
    @8
    @2
    cn
    wcel
    #
    @14
    @9
    @17
    @2
    @6
    wcel
    #
    wn
    #
    @9
    @8
    @17
    @19
    wa
    @1
    @8
    simpr
    @2
    cn
    @6
    eldif
    sylib
    #
    simpld
    #
    @1
    cn
    cn0
    @2
    cA
    @1
    cn
    cn0
    cA
    wf
    #
    cA
    ccnv
    cn
    cima
    #
    cfn
    wcel
    #
    cA
    cR
    cS
    vf
    vk
    eulerpartlems.r
    eulerpartlems.s
    eulerpartlemelr
    #
    simpld
    #
    ffvelrnda
    syldan
    @9
    @1
    @17
    @3
    @2
    clt
    wbr
    #
    @16
    @1
    @8
    simpl
    @21
    @9
    @17
    @12
    @19
    @27
    @21
    @1
    @12
    @8
    @13
    adantr
    @9
    @17
    @19
    @20
    simprd
    @17
    @12
    wa
    #
    @19
    @27
    @28
    @19
    @2
    @3
    cle
    wbr
    #
    wn
    @27
    @28
    @18
    @29
    @28
    @2
    c1
    cuz
    cfv
    #
    wcel
    @3
    cz
    wcel
    @18
    @29
    wb
    @28
    @2
    cn
    @30
    @17
    @12
    simpl
    #
    nnuz
    syl6eleq
    @28
    @3
    @17
    @12
    simpr
    #
    nn0zd
    @2
    c1
    @3
    elfz5
    syl2anc
    notbid
    @28
    @3
    @2
    @28
    @3
    @32
    nn0red
    @28
    @2
    @31
    nnred
    ltnled
    bitr4d
    biimpa
    syl21anc
    @1
    @17
    wa
    @27
    @16
    @1
    @27
    @16
    wi
    #
    vt
    cn
    @1
    @27
    @15
    wa
    #
    wn
    #
    vt
    cn
    wral
    #
    @33
    vt
    cn
    wral
    @1
    @34
    vt
    cn
    wrex
    #
    wn
    #
    @36
    @1
    cn
    @10
    @2
    cmul
    co
    #
    vt
    csu
    #
    @3
    wceq
    @38
    @1
    @3
    cn
    vk
    cv
    #
    cA
    cfv
    #
    @41
    cmul
    co
    #
    vk
    csu
    @40
    cA
    cR
    cS
    vf
    vk
    eulerpartlems.r
    eulerpartlems.s
    eulerpartlemsv1
    cn
    @43
    @39
    vk
    vt
    @41
    @2
    wceq
    #
    @42
    @10
    @41
    @2
    cmul
    @41
    @2
    cA
    fveq2
    @44
    id
    oveq12d
    cbvsumv
    syl6req
    @1
    @37
    @40
    @3
    @37
    @3
    vl
    cv
    #
    clt
    wbr
    #
    cc0
    @45
    cA
    cfv
    #
    clt
    wbr
    #
    wa
    #
    vl
    cn
    wrex
    #
    @1
    @40
    @3
    wne
    #
    @34
    @49
    vt
    vl
    cn
    @2
    @45
    wceq
    #
    @27
    @46
    @15
    @48
    @2
    @45
    @3
    clt
    breq2
    @52
    @10
    @47
    cc0
    clt
    @2
    @45
    cA
    fveq2
    #
    breq2d
    anbi12d
    cbvrexv
    @1
    @50
    @51
    @1
    @50
    wa
    #
    @3
    @40
    @54
    @3
    @1
    @12
    @50
    @13
    adantr
    nn0red
    @1
    @49
    @3
    @40
    clt
    wbr
    vl
    cn
    @1
    @45
    cn
    wcel
    #
    wa
    #
    @49
    wa
    #
    @3
    @45
    @40
    @57
    @3
    @1
    @12
    @55
    @49
    @13
    ad2antrr
    nn0red
    @57
    @45
    @56
    @55
    @49
    @1
    @55
    simpr
    #
    adantr
    #
    nnred
    #
    @56
    @40
    cr
    wcel
    @49
    @56
    @39
    vt
    vm
    cn
    vm
    cv
    #
    cA
    cfv
    #
    @61
    cmul
    co
    #
    cmpt
    #
    c1
    cn
    nnuz
    @56
    1zzd
    #
    @56
    @17
    wa
    #
    @22
    @17
    @2
    @64
    cfv
    @39
    wceq
    @1
    @22
    @55
    @17
    @26
    ad2antrr
    @56
    @17
    simpr
    #
    @22
    @17
    wa
    #
    vm
    @2
    @63
    @39
    cn
    @64
    cn0
    @68
    @64
    eqidd
    @68
    @61
    @2
    wceq
    #
    wa
    #
    @62
    @10
    @61
    @2
    cmul
    @70
    @61
    @2
    cA
    @68
    @69
    simpr
    #
    fveq2d
    @71
    oveq12d
    @22
    @17
    simpr
    #
    @68
    @10
    @2
    cn
    cn0
    @2
    cA
    ffvelrn
    @68
    @2
    @72
    nnnn0d
    nn0mulcld
    fvmptd
    syl2anc
    #
    @66
    @39
    @66
    @10
    @2
    @56
    cn
    cn0
    @2
    cA
    @1
    @22
    @55
    @26
    adantr
    #
    ffvelrnda
    @66
    @2
    @67
    nnnn0d
    nn0mulcld
    #
    nn0red
    #
    @56
    cn
    @64
    c1
    nnuz
    @65
    @56
    cn
    cn0
    @64
    wf
    cn0
    cc
    wss
    cn
    cc
    @64
    wf
    #
    @56
    vt
    cn
    @39
    cn0
    @64
    @75
    vm
    vt
    cn
    @63
    @39
    @69
    @62
    @10
    @61
    @2
    cmul
    @61
    @2
    cA
    fveq2
    @69
    id
    oveq12d
    cbvmptv
    #
    fmptd
    nn0sscn
    cn
    cn0
    cc
    @64
    fss
    sylancl
    #
    @56
    @64
    cc0
    csupp
    co
    #
    @64
    ccnv
    cc
    cc0
    csn
    cdif
    #
    cima
    #
    cfn
    @56
    @77
    @80
    @82
    wceq
    #
    @79
    cn
    cvv
    wcel
    #
    cc0
    cn0
    wcel
    #
    @77
    @83
    nnex
    0nn0
    cn
    cc
    @81
    @64
    cvv
    cn0
    cc0
    @81
    eqid
    ffs2
    mp3an12
    syl
    @56
    cA
    cc0
    csupp
    co
    #
    cfn
    wcel
    @80
    @86
    wss
    #
    @80
    cfn
    wcel
    @56
    @86
    @23
    cfn
    @56
    @84
    @22
    @86
    @23
    wceq
    nnex
    @74
    cA
    cn
    cvv
    frnnn0supp
    sylancr
    @1
    @24
    @55
    @1
    @22
    @24
    @25
    simprd
    adantr
    eqeltrd
    @56
    @22
    @87
    @74
    @22
    vt
    cn
    @39
    cA
    @64
    cvv
    cn0
    cc0
    @78
    @84
    @22
    nnex
    a1i
    @85
    @22
    0nn0
    a1i
    cn
    cn0
    cA
    ffn
    @22
    @17
    @11
    w3a
    #
    @39
    cc0
    @2
    cmul
    co
    cc0
    @88
    @10
    cc0
    @2
    cmul
    @22
    @17
    @11
    simp3
    oveq1d
    @88
    @2
    @88
    @2
    @22
    @17
    @11
    simp2
    nncnd
    mul02d
    eqtrd
    suppss3
    syl
    @86
    @80
    ssfi
    syl2anc
    eqeltrrd
    fsumcvg4
    #
    isumrecl
    adantr
    #
    @56
    @46
    @48
    simprl
    @57
    @45
    @47
    @45
    cmul
    co
    #
    @40
    @60
    @57
    @47
    @45
    @57
    @47
    @56
    @47
    cn0
    wcel
    #
    @49
    @1
    cn
    cn0
    @45
    cA
    @26
    ffvelrnda
    #
    adantr
    #
    nn0red
    #
    @60
    remulcld
    @90
    @57
    @45
    @47
    @60
    @95
    @57
    @45
    @57
    @45
    @59
    nnnn0d
    nn0ge0d
    @57
    @92
    @48
    c1
    @47
    cle
    wbr
    #
    @94
    @56
    @46
    @48
    simprr
    @92
    @48
    wa
    @47
    cn
    wcel
    @96
    @47
    elnnnn0b
    @47
    nnge1
    sylbir
    syl2anc
    lemulge12d
    @56
    @91
    @40
    cle
    wbr
    @49
    @56
    @45
    csn
    #
    @39
    vt
    csu
    #
    @91
    @40
    cle
    @56
    @55
    @91
    cc
    wcel
    @98
    @91
    wceq
    @58
    @56
    @47
    @45
    @56
    @47
    @93
    nn0cnd
    @56
    @45
    @58
    nncnd
    mulcld
    @39
    @91
    vt
    @45
    cn
    @52
    @10
    @47
    @2
    @45
    cmul
    @53
    @52
    id
    oveq12d
    sumsn
    syl2anc
    @56
    @97
    @39
    vt
    @64
    c1
    cn
    nnuz
    @65
    @97
    cfn
    wcel
    @56
    @45
    snfi
    a1i
    @56
    @45
    cn
    @58
    snssd
    @73
    @76
    @66
    @39
    @75
    nn0ge0d
    @89
    isumless
    eqbrtrrd
    adantr
    letrd
    ltletrd
    r19.29an
    gtned
    ex
    syl5bi
    necon2bd
    mpd
    @34
    vt
    cn
    ralnex
    sylibr
    @33
    @35
    vt
    cn
    @27
    @15
    imnan
    ralbii
    sylibr
    r19.21bi
    imp
    syl21anc
    @14
    @16
    @11
    @14
    @10
    cc0
    cle
    wbr
    @16
    @11
    @14
    @10
    cc0
    @10
    nn0re
    @14
    0red
    lenltd
    @10
    nn0le0eq0
    bitr3d
    biimpa
    syl2anc
    sylbir
end
