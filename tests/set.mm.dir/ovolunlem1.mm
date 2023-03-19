include "cun.mm"
include "covol.mm"
include "cfv.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "caddc.mm"
include "co.mm"
include "cr.mm"
include "wss.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "simpld.mm"
include "unssd.mm"
include "c0.mm"
include "wne.mm"
include "cpnf.mm"
include "cn.mm"
include "wf.mm"
include "cc0.mm"
include "cico.mm"
include "cxp.mm"
include "cin.mm"
include "cv.mm"
include "c2.mm"
include "cdiv.mm"
include "c1.mm"
include "cif.mm"
include "wa.mm"
include "cmap.mm"
include "reex.mm"
include "xpex.mm"
include "inex2.mm"
include "nnex.mm"
include "elmap.mm"
include "sylib.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "wn.mm"
include "wb.mm"
include "nneo.mm"
include "adantl.mm"
include "con2bid.mm"
include "biimpar.mm"
include "syldan.mm"
include "ifclda.mm"
include "fmptd.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "eqid.mm"
include "ovolsf.mm"
include "syl.mm"
include "rge0ssre.mm"
include "fss.mm"
include "sylancl.mm"
include "frn.mm"
include "cdm.mm"
include "1nn.mm"
include "wfn.mm"
include "wceq.mm"
include "cseq.mm"
include "cuz.mm"
include "cz.mm"
include "1z.mm"
include "seqfn.mm"
include "mp1i.mm"
include "fneq1i.mm"
include "nnuz.mm"
include "fneq2i.mm"
include "bitri.mm"
include "sylibr.mm"
include "fndm.mm"
include "syl5eleqr.mm"
include "ne0i.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "wral.mm"
include "wrex.mm"
include "simprd.mm"
include "readdcld.mm"
include "rpred.mm"
include "ovolunlem1a.mm"
include "ralrimiva.mm"
include "breq1.mm"
include "ralrn.mm"
include "mpbird.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "supxrbnd2.mm"
include "mpbid.mm"
include "supxrbnd.mm"
include "syl3anc.mm"
include "cioo.mm"
include "cuni.mm"
include "c1st.mm"
include "c2nd.mm"
include "cmul.mm"
include "cc.mm"
include "nncn.mm"
include "2timesd.mm"
include "oveq1d.mm"
include "1cnd.mm"
include "addsubassd.mm"
include "eqtrd.mm"
include "cn0.mm"
include "simpr.mm"
include "nnm1nn0.mm"
include "nnnn0addcl.mm"
include "eqeltrd.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "fveq2d.mm"
include "ifbieq12d.mm"
include "fvex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "2nn.mm"
include "nnmulcl.mm"
include "sylancr.mm"
include "nncnd.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "2cn.mm"
include "2ne0.mm"
include "divcan3.mm"
include "mp3an23.mm"
include "iffalsed.mm"
include "3eqtrd.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "breq1d.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "biimprcd.mm"
include "reximdv.mm"
include "syl5com.mm"
include "rexlimdva.mm"
include "ralimdv.mm"
include "ovolfioo.mm"
include "3imtr4d.mm"
include "mpd.mm"
include "iftrued.mm"
include "ovollb.mm"
include "ovollecl.mm"
include "rexrd.mm"
include "supxrleub.mm"
include "letrd.mm"

theorem ovolunlem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cT: class T
  let cU: class U
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vz: setvar z
  let vm: setvar m
  let vj: setvar j
  assume ovolun.a: |- ( ph -> ( A C_ RR /\ ( vol* ` A ) e. RR ) )
  assume ovolun.b: |- ( ph -> ( B C_ RR /\ ( vol* ` B ) e. RR ) )
  assume ovolun.c: |- ( ph -> C e. RR+ )
  assume ovolun.s: |- S = seq 1 ( + , ( ( abs o. - ) o. F ) )
  assume ovolun.t: |- T = seq 1 ( + , ( ( abs o. - ) o. G ) )
  assume ovolun.u: |- U = seq 1 ( + , ( ( abs o. - ) o. H ) )
  assume ovolun.f1: |- ( ph -> F e. ( ( <_ i^i ( RR X. RR ) ) ^m NN ) )
  assume ovolun.f2: |- ( ph -> A C_ U. ran ( (,) o. F ) )
  assume ovolun.f3: |- ( ph -> sup ( ran S , RR* , < ) <_ ( ( vol* ` A ) + ( C / 2 ) ) )
  assume ovolun.g1: |- ( ph -> G e. ( ( <_ i^i ( RR X. RR ) ) ^m NN ) )
  assume ovolun.g2: |- ( ph -> B C_ U. ran ( (,) o. G ) )
  assume ovolun.g3: |- ( ph -> sup ( ran T , RR* , < ) <_ ( ( vol* ` B ) + ( C / 2 ) ) )
  assume ovolun.h: |- H = ( n e. NN |-> if ( ( n / 2 ) e. NN , ( G ` ( n / 2 ) ) , ( F ` ( ( n + 1 ) / 2 ) ) ) )

  disjoint C n
  disjoint F n
  disjoint A n
  disjoint B n
  disjoint G n
  disjoint n ph
  disjoint g h
  disjoint g k
  disjoint g n
  disjoint g z
  disjoint C g
  disjoint h k
  disjoint h n
  disjoint h z
  disjoint C h
  disjoint k n
  disjoint k z
  disjoint C k
  disjoint n z
  disjoint C z
  disjoint k m
  disjoint F k
  disjoint m n
  disjoint m z
  disjoint F m
  disjoint F z
  disjoint j k
  disjoint j m
  disjoint j z
  disjoint H j
  disjoint H k
  disjoint H m
  disjoint H z
  disjoint g m
  disjoint A g
  disjoint h m
  disjoint A h
  disjoint A k
  disjoint A m
  disjoint A z
  disjoint B g
  disjoint B h
  disjoint B k
  disjoint B m
  disjoint B z
  disjoint S k
  disjoint S z
  disjoint T k
  disjoint T z
  disjoint G k
  disjoint G m
  disjoint G z
  disjoint g j
  disjoint g ph
  disjoint h j
  disjoint h ph
  disjoint j n
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph z
  disjoint U k
  disjoint U z
  assert |- ( ph -> ( vol* ` ( A u. B ) ) <_ ( ( ( vol* ` A ) + ( vol* ` B ) ) + C ) )

  proof
    wph
    cA
    cB
    cun
    #
    covol
    cfv
    #
    cU
    crn
    #
    cxr
    clt
    csup
    #
    cA
    covol
    cfv
    #
    cB
    covol
    cfv
    #
    caddc
    co
    #
    cC
    caddc
    co
    #
    wph
    @0
    cr
    wss
    @3
    cr
    wcel
    #
    @1
    @3
    cle
    wbr
    #
    @1
    cr
    wcel
    wph
    cA
    cB
    cr
    wph
    cA
    cr
    wss
    #
    @4
    cr
    wcel
    #
    ovolun.a
    simpld
    #
    wph
    cB
    cr
    wss
    #
    @5
    cr
    wcel
    #
    ovolun.b
    simpld
    #
    unssd
    wph
    @2
    cr
    wss
    #
    @2
    c0
    wne
    #
    @3
    cpnf
    clt
    wbr
    #
    @8
    wph
    cn
    cr
    cU
    wf
    #
    @16
    wph
    cn
    cc0
    cpnf
    cico
    co
    #
    cU
    wf
    #
    @20
    cr
    wss
    @19
    wph
    cn
    cle
    cr
    cr
    cxp
    #
    cin
    #
    cH
    wf
    #
    @21
    wph
    vn
    cn
    vn
    cv
    #
    c2
    cdiv
    co
    #
    cn
    wcel
    #
    @26
    cG
    cfv
    #
    @25
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cF
    cfv
    #
    cif
    #
    @23
    cH
    wph
    @25
    cn
    wcel
    #
    wa
    #
    @27
    @28
    @31
    @23
    @34
    cn
    @23
    @26
    cG
    wph
    cn
    @23
    cG
    wf
    #
    @33
    wph
    cG
    @23
    cn
    cmap
    co
    #
    wcel
    @35
    ovolun.g1
    @23
    cn
    cG
    @22
    cle
    cr
    cr
    reex
    reex
    xpex
    inex2
    #
    nnex
    elmap
    sylib
    #
    adantr
    ffvelrnda
    @34
    @27
    wn
    #
    @30
    cn
    wcel
    #
    @31
    @23
    wcel
    @34
    @40
    @39
    @34
    @27
    @40
    @33
    @27
    @40
    wn
    wb
    wph
    @25
    nneo
    adantl
    con2bid
    biimpar
    @34
    cn
    @23
    @30
    cF
    wph
    cn
    @23
    cF
    wf
    #
    @33
    wph
    cF
    @36
    wcel
    @41
    ovolun.f1
    @23
    cn
    cF
    @37
    nnex
    elmap
    sylib
    #
    adantr
    ffvelrnda
    syldan
    ifclda
    ovolun.h
    fmptd
    #
    cU
    cH
    cabs
    cmin
    ccom
    cH
    ccom
    #
    @44
    eqid
    ovolun.u
    ovolsf
    syl
    rge0ssre
    cn
    @20
    cr
    cU
    fss
    sylancl
    cn
    cr
    cU
    frn
    syl
    #
    wph
    cU
    cdm
    #
    c0
    wne
    #
    @17
    wph
    c1
    @46
    wcel
    @47
    wph
    c1
    cn
    @46
    1nn
    wph
    cU
    cn
    wfn
    #
    @46
    cn
    wceq
    wph
    caddc
    @44
    c1
    cseq
    #
    c1
    cuz
    cfv
    #
    wfn
    #
    @48
    c1
    cz
    wcel
    @51
    wph
    1z
    caddc
    @44
    c1
    seqfn
    mp1i
    @48
    @49
    cn
    wfn
    @51
    cn
    cU
    @49
    ovolun.u
    fneq1i
    cn
    @50
    @49
    nnuz
    fneq2i
    bitri
    sylibr
    #
    cn
    cU
    fndm
    syl
    syl5eleqr
    @46
    c1
    ne0i
    syl
    @46
    c0
    @2
    c0
    cU
    dm0rn0
    necon3bii
    sylib
    wph
    vz
    cv
    #
    vk
    cv
    #
    cle
    wbr
    #
    vz
    @2
    wral
    #
    vk
    cr
    wrex
    #
    @18
    wph
    @7
    cr
    wcel
    @53
    @7
    cle
    wbr
    #
    vz
    @2
    wral
    #
    @57
    wph
    @6
    cC
    wph
    @4
    @5
    wph
    @10
    @11
    ovolun.a
    simprd
    wph
    @13
    @14
    ovolun.b
    simprd
    readdcld
    wph
    cC
    ovolun.c
    rpred
    readdcld
    #
    wph
    @59
    @54
    cU
    cfv
    #
    @7
    cle
    wbr
    #
    vk
    cn
    wral
    #
    wph
    @62
    vk
    cn
    wph
    cA
    cB
    cC
    cS
    cT
    cU
    vk
    vn
    cF
    cG
    cH
    ovolun.a
    ovolun.b
    ovolun.c
    ovolun.s
    ovolun.t
    ovolun.u
    ovolun.f1
    ovolun.f2
    ovolun.f3
    ovolun.g1
    ovolun.g2
    ovolun.g3
    ovolun.h
    ovolunlem1a
    ralrimiva
    wph
    @48
    @59
    @63
    wb
    @52
    @58
    @62
    vz
    vk
    cn
    cU
    @53
    @61
    @7
    cle
    breq1
    ralrn
    syl
    mpbird
    #
    @56
    @59
    vk
    @7
    cr
    @54
    @7
    wceq
    @55
    @58
    vz
    @2
    @54
    @7
    @53
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    wph
    @2
    cxr
    wss
    #
    @57
    @18
    wb
    wph
    @2
    cr
    cxr
    @45
    ressxr
    syl6ss
    #
    vk
    vz
    @2
    supxrbnd2
    syl
    mpbid
    @2
    supxrbnd
    syl3anc
    #
    wph
    @24
    @0
    cioo
    cH
    ccom
    crn
    cuni
    #
    wss
    @9
    @43
    wph
    cA
    cB
    @68
    wph
    cA
    cioo
    cF
    ccom
    crn
    cuni
    wss
    #
    cA
    @68
    wss
    #
    ovolun.f2
    wph
    vm
    cv
    #
    cF
    cfv
    #
    c1st
    cfv
    #
    @53
    clt
    wbr
    #
    @53
    @72
    c2nd
    cfv
    #
    clt
    wbr
    #
    wa
    #
    vm
    cn
    wrex
    #
    vz
    cA
    wral
    #
    @54
    cH
    cfv
    #
    c1st
    cfv
    #
    @53
    clt
    wbr
    #
    @53
    @80
    c2nd
    cfv
    #
    clt
    wbr
    #
    wa
    #
    vk
    cn
    wrex
    #
    vz
    cA
    wral
    #
    @69
    @70
    wph
    @78
    @86
    vz
    cA
    wph
    @77
    @86
    vm
    cn
    wph
    @71
    cn
    wcel
    #
    wa
    #
    @80
    @72
    wceq
    #
    vk
    cn
    wrex
    #
    @77
    @86
    @89
    c2
    @71
    cmul
    co
    #
    c1
    cmin
    co
    #
    cn
    wcel
    #
    @93
    cH
    cfv
    #
    @72
    wceq
    #
    @91
    @89
    @93
    @71
    @71
    c1
    cmin
    co
    #
    caddc
    co
    #
    cn
    @89
    @93
    @71
    @71
    caddc
    co
    #
    c1
    cmin
    co
    @98
    @89
    @92
    @99
    c1
    cmin
    @89
    @71
    @88
    @71
    cc
    wcel
    #
    wph
    @71
    nncn
    adantl
    #
    2timesd
    oveq1d
    @89
    @71
    @71
    c1
    @101
    @101
    @89
    1cnd
    addsubassd
    eqtrd
    @89
    @88
    @97
    cn0
    wcel
    #
    @98
    cn
    wcel
    wph
    @88
    simpr
    #
    @88
    @102
    wph
    @71
    nnm1nn0
    adantl
    @71
    @97
    nnnn0addcl
    syl2anc
    eqeltrd
    #
    @89
    @95
    @93
    c2
    cdiv
    co
    #
    cn
    wcel
    #
    @105
    cG
    cfv
    #
    @93
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cF
    cfv
    #
    cif
    #
    @110
    @72
    @89
    @94
    @95
    @111
    wceq
    @104
    vn
    @93
    @32
    @111
    cn
    cH
    @25
    @93
    wceq
    #
    @27
    @106
    @28
    @31
    @107
    @110
    @112
    @26
    @105
    cn
    @25
    @93
    c2
    cdiv
    oveq1
    #
    eleq1d
    @112
    @26
    @105
    cG
    @113
    fveq2d
    @112
    @30
    @109
    cF
    @112
    @29
    @108
    c2
    cdiv
    @25
    @93
    c1
    caddc
    oveq1
    oveq1d
    fveq2d
    ifbieq12d
    ovolun.h
    @106
    @107
    @110
    @105
    cG
    fvex
    @109
    cF
    fvex
    ifex
    fvmpt
    syl
    @89
    @106
    @107
    @110
    @89
    @109
    cn
    wcel
    #
    @106
    wn
    @89
    @109
    @71
    cn
    @89
    @109
    @92
    c2
    cdiv
    co
    #
    @71
    @89
    @108
    @92
    c2
    cdiv
    @89
    @92
    cc
    wcel
    c1
    cc
    wcel
    @108
    @92
    wceq
    @89
    @92
    @89
    c2
    cn
    wcel
    @88
    @92
    cn
    wcel
    #
    2nn
    @103
    c2
    @71
    nnmulcl
    sylancr
    #
    nncnd
    ax-1cn
    @92
    c1
    npcan
    sylancl
    oveq1d
    @89
    @100
    @115
    @71
    wceq
    #
    @101
    @100
    c2
    cc
    wcel
    c2
    cc0
    wne
    @118
    2cn
    2ne0
    @71
    c2
    divcan3
    mp3an23
    syl
    #
    eqtrd
    #
    @103
    eqeltrd
    @89
    @106
    @114
    @89
    @94
    @106
    @114
    wn
    wb
    @104
    @93
    nneo
    syl
    con2bid
    mpbid
    iffalsed
    @89
    @109
    @71
    cF
    @120
    fveq2d
    3eqtrd
    @90
    @96
    vk
    @93
    cn
    @54
    @93
    wceq
    @80
    @95
    @72
    @54
    @93
    cH
    fveq2
    eqeq1d
    rspcev
    syl2anc
    @77
    @90
    @85
    vk
    cn
    @90
    @85
    @77
    @90
    @82
    @74
    @84
    @76
    @90
    @81
    @73
    @53
    clt
    @80
    @72
    c1st
    fveq2
    breq1d
    @90
    @83
    @75
    @53
    clt
    @80
    @72
    c2nd
    fveq2
    breq2d
    anbi12d
    biimprcd
    reximdv
    syl5com
    rexlimdva
    ralimdv
    wph
    @10
    @41
    @69
    @79
    wb
    @12
    @42
    vz
    cA
    vm
    cF
    ovolfioo
    syl2anc
    wph
    @10
    @24
    @70
    @87
    wb
    @12
    @43
    vz
    cA
    vk
    cH
    ovolfioo
    syl2anc
    3imtr4d
    mpd
    wph
    cB
    cioo
    cG
    ccom
    crn
    cuni
    wss
    #
    cB
    @68
    wss
    #
    ovolun.g2
    wph
    @71
    cG
    cfv
    #
    c1st
    cfv
    #
    @53
    clt
    wbr
    #
    @53
    @123
    c2nd
    cfv
    #
    clt
    wbr
    #
    wa
    #
    vm
    cn
    wrex
    #
    vz
    cB
    wral
    #
    @86
    vz
    cB
    wral
    #
    @121
    @122
    wph
    @129
    @86
    vz
    cB
    wph
    @128
    @86
    vm
    cn
    @89
    @80
    @123
    wceq
    #
    vk
    cn
    wrex
    #
    @128
    @86
    @89
    @116
    @92
    cH
    cfv
    #
    @123
    wceq
    #
    @133
    @117
    @89
    @134
    @115
    cn
    wcel
    #
    @115
    cG
    cfv
    #
    @92
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cF
    cfv
    #
    cif
    #
    @137
    @123
    @89
    @116
    @134
    @141
    wceq
    @117
    vn
    @92
    @32
    @141
    cn
    cH
    @25
    @92
    wceq
    #
    @27
    @136
    @28
    @31
    @137
    @140
    @142
    @26
    @115
    cn
    @25
    @92
    c2
    cdiv
    oveq1
    #
    eleq1d
    @142
    @26
    @115
    cG
    @143
    fveq2d
    @142
    @30
    @139
    cF
    @142
    @29
    @138
    c2
    cdiv
    @25
    @92
    c1
    caddc
    oveq1
    oveq1d
    fveq2d
    ifbieq12d
    ovolun.h
    @136
    @137
    @140
    @115
    cG
    fvex
    @139
    cF
    fvex
    ifex
    fvmpt
    syl
    @89
    @136
    @137
    @140
    @89
    @115
    @71
    cn
    @119
    @103
    eqeltrd
    iftrued
    @89
    @115
    @71
    cG
    @119
    fveq2d
    3eqtrd
    @132
    @135
    vk
    @92
    cn
    @54
    @92
    wceq
    @80
    @134
    @123
    @54
    @92
    cH
    fveq2
    eqeq1d
    rspcev
    syl2anc
    @128
    @132
    @85
    vk
    cn
    @132
    @85
    @128
    @132
    @82
    @125
    @84
    @127
    @132
    @81
    @124
    @53
    clt
    @80
    @123
    c1st
    fveq2
    breq1d
    @132
    @83
    @126
    @53
    clt
    @80
    @123
    c2nd
    fveq2
    breq2d
    anbi12d
    biimprcd
    reximdv
    syl5com
    rexlimdva
    ralimdv
    wph
    @13
    @35
    @121
    @130
    wb
    @15
    @38
    vz
    cB
    vm
    cG
    ovolfioo
    syl2anc
    wph
    @13
    @24
    @122
    @131
    wb
    @15
    @43
    vz
    cB
    vk
    cH
    ovolfioo
    syl2anc
    3imtr4d
    mpd
    unssd
    @0
    cU
    cH
    ovolun.u
    ovollb
    syl2anc
    #
    @0
    @3
    ovollecl
    syl3anc
    @67
    @60
    @144
    wph
    @3
    @7
    cle
    wbr
    #
    @59
    @64
    wph
    @65
    @7
    cxr
    wcel
    @145
    @59
    wb
    @66
    wph
    @7
    @60
    rexrd
    vz
    @2
    @7
    supxrleub
    syl2anc
    mpbird
    letrd
end
