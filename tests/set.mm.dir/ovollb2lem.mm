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
include "cicc.mm"
include "ccom.mm"
include "cuni.mm"
include "cn.mm"
include "cle.mm"
include "cxp.mm"
include "cin.mm"
include "wf.mm"
include "ovolficcss.mm"
include "syl.mm"
include "sstrd.mm"
include "ovolcl.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "cv.mm"
include "c1st.mm"
include "c2.mm"
include "cdiv.mm"
include "cexp.mm"
include "cmin.mm"
include "c2nd.mm"
include "cop.mm"
include "wa.mm"
include "wbr.mm"
include "w3a.mm"
include "ovolfcl.mm"
include "sylan.mm"
include "simp1d.mm"
include "crp.mm"
include "rphalfcld.mm"
include "adantr.mm"
include "cn0.mm"
include "2nn.mm"
include "nnnn0.mm"
include "adantl.mm"
include "nnexpcl.mm"
include "sylancr.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "rpred.mm"
include "resubcld.mm"
include "simp2d.mm"
include "readdcld.mm"
include "ltsubrpd.mm"
include "simp3d.mm"
include "ltaddrpd.mm"
include "lelttrd.mm"
include "lttrd.mm"
include "ltled.mm"
include "df-br.mm"
include "sylib.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "elind.mm"
include "fmptd.mm"
include "cabs.mm"
include "eqid.mm"
include "ovolsf.mm"
include "frn.mm"
include "icossxr.mm"
include "syl6ss.mm"
include "supxrcl.mm"
include "rexrd.mm"
include "cioo.mm"
include "wrex.mm"
include "wral.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "opeq12d.mm"
include "opex.mm"
include "fvmpt.mm"
include "ovex.mm"
include "op1st.mm"
include "syl6eq.mm"
include "eqbrtrd.mm"
include "adantlr.mm"
include "wi.mm"
include "sselda.mm"
include "ltletr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "op2nd.mm"
include "breqtrrd.mm"
include "lelttr.mm"
include "mpan2d.mm"
include "anim12d.mm"
include "reximdva.mm"
include "ralimdva.mm"
include "wb.mm"
include "ovolficc.mm"
include "ovolfioo.mm"
include "3imtr4d.mm"
include "mpd.mm"
include "ovollb.mm"
include "c1.mm"
include "cseq.mm"
include "fveq1i.mm"
include "cfz.mm"
include "csu.mm"
include "fzfid.mm"
include "rge0ssre.mm"
include "ovolfsf.mm"
include "elfznn.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "sseldi.mm"
include "recnd.mm"
include "cc.mm"
include "rpcnd.mm"
include "sylan2.mm"
include "fsumadd.mm"
include "ovolfsval.mm"
include "subcld.mm"
include "addsubassd.mm"
include "subadd23d.mm"
include "oveq1d.mm"
include "subsub3d.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divdird.mm"
include "2halvesd.mm"
include "eqtr3d.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "cuz.mm"
include "simpr.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "addcld.mm"
include "fsumser.mm"
include "eqidd.mm"
include "syl6eqr.mm"
include "geo2sum.mm"
include "3eqtr3d.mm"
include "syl5eq.mm"
include "ffvelrnda.mm"
include "wfn.mm"
include "ffn.mm"
include "fnfvelrn.mm"
include "supxrub.mm"
include "le2addd.mm"
include "ralrimiva.mm"
include "breq1.mm"
include "ralrn.mm"
include "3syl.mm"
include "mpbird.mm"
include "supxrleub.mm"
include "xrletrd.mm"

theorem ovollb2lem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  let cN: class N
  let vk: setvar k
  assume ovollb2.1: |- S = seq 1 ( + , ( ( abs o. - ) o. F ) )
  assume ovollb2.2: |- G = ( n e. NN |-> <. ( ( 1st ` ( F ` n ) ) - ( ( B / 2 ) / ( 2 ^ n ) ) ) , ( ( 2nd ` ( F ` n ) ) + ( ( B / 2 ) / ( 2 ^ n ) ) ) >. )
  assume ovollb2.3: |- T = seq 1 ( + , ( ( abs o. - ) o. G ) )
  assume ovollb2.4: |- ( ph -> F : NN --> ( <_ i^i ( RR X. RR ) ) )
  assume ovollb2.5: |- ( ph -> A C_ U. ran ( [,] o. F ) )
  assume ovollb2.6: |- ( ph -> B e. RR+ )
  assume ovollb2.7: |- ( ph -> sup ( ran S , RR* , < ) e. RR )

  disjoint A n
  disjoint F n
  disjoint B n
  disjoint n ph
  disjoint S n
  disjoint f g
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F f
  disjoint F m
  disjoint F x
  disjoint F z
  disjoint G m
  disjoint G z
  disjoint M x
  disjoint N x
  disjoint f k
  disjoint B f
  disjoint g k
  disjoint B g
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint B k
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint k z
  disjoint k ph
  disjoint m ph
  disjoint ph z
  disjoint S f
  disjoint S k
  disjoint S x
  disjoint S y
  disjoint T k
  disjoint T y
  assert |- ( ph -> ( vol* ` A ) <_ ( sup ( ran S , RR* , < ) + B ) )

  proof
    wph
    cA
    covol
    cfv
    #
    cT
    crn
    #
    cxr
    clt
    csup
    #
    cS
    crn
    #
    cxr
    clt
    csup
    #
    cB
    caddc
    co
    #
    wph
    cA
    cr
    wss
    #
    @0
    cxr
    wcel
    wph
    cA
    cicc
    cF
    ccom
    crn
    cuni
    #
    cr
    ovollb2.5
    wph
    cn
    cle
    cr
    cr
    cxp
    #
    cin
    #
    cF
    wf
    #
    @7
    cr
    wss
    ovollb2.4
    cF
    ovolficcss
    syl
    sstrd
    #
    cA
    ovolcl
    syl
    wph
    @1
    cxr
    wss
    #
    @2
    cxr
    wcel
    wph
    @1
    cc0
    cpnf
    cico
    co
    #
    cxr
    wph
    cn
    @13
    cT
    wf
    #
    @1
    @13
    wss
    wph
    cn
    @9
    cG
    wf
    #
    @14
    wph
    vn
    cn
    vn
    cv
    #
    cF
    cfv
    #
    c1st
    cfv
    #
    cB
    c2
    cdiv
    co
    #
    c2
    @16
    cexp
    co
    #
    cdiv
    co
    #
    cmin
    co
    #
    @17
    c2nd
    cfv
    #
    @21
    caddc
    co
    #
    cop
    #
    @9
    cG
    wph
    @16
    cn
    wcel
    #
    wa
    #
    cle
    @8
    @25
    @27
    @22
    @24
    cle
    wbr
    @25
    cle
    wcel
    @27
    @22
    @24
    @27
    @18
    @21
    @27
    @18
    cr
    wcel
    #
    @23
    cr
    wcel
    #
    @18
    @23
    cle
    wbr
    #
    wph
    @10
    @26
    @28
    @29
    @30
    w3a
    ovollb2.4
    cF
    @16
    ovolfcl
    sylan
    #
    simp1d
    #
    @27
    @21
    @27
    @19
    @20
    wph
    @19
    crp
    wcel
    #
    @26
    wph
    cB
    ovollb2.6
    rphalfcld
    #
    adantr
    @27
    @20
    @27
    c2
    cn
    wcel
    #
    @16
    cn0
    wcel
    #
    @20
    cn
    wcel
    2nn
    @26
    @36
    wph
    @16
    nnnn0
    adantl
    c2
    @16
    nnexpcl
    sylancr
    nnrpd
    rpdivcld
    #
    rpred
    #
    resubcld
    #
    @27
    @23
    @21
    @27
    @28
    @29
    @30
    @31
    simp2d
    #
    @38
    readdcld
    #
    @27
    @22
    @18
    @24
    @39
    @32
    @41
    @27
    @18
    @21
    @32
    @37
    ltsubrpd
    @27
    @18
    @23
    @24
    @32
    @40
    @41
    @27
    @28
    @29
    @30
    @31
    simp3d
    @27
    @23
    @21
    @40
    @37
    ltaddrpd
    lelttrd
    lttrd
    ltled
    @22
    @24
    cle
    df-br
    sylib
    @27
    @22
    cr
    wcel
    @24
    cr
    wcel
    @25
    @8
    wcel
    @39
    @41
    @22
    @24
    cr
    cr
    opelxpi
    syl2anc
    elind
    ovollb2.2
    fmptd
    #
    cT
    cG
    cabs
    cmin
    ccom
    #
    cG
    ccom
    #
    @44
    eqid
    #
    ovollb2.3
    ovolsf
    syl
    #
    cn
    @13
    cT
    frn
    syl
    cc0
    cpnf
    icossxr
    #
    syl6ss
    #
    @1
    supxrcl
    syl
    wph
    @5
    wph
    @4
    cB
    ovollb2.7
    wph
    cB
    ovollb2.6
    rpred
    readdcld
    rexrd
    #
    wph
    @15
    cA
    cioo
    cG
    ccom
    crn
    cuni
    wss
    #
    @0
    @2
    cle
    wbr
    @42
    wph
    cA
    @7
    wss
    #
    @50
    ovollb2.5
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
    vz
    cv
    #
    cle
    wbr
    #
    @55
    @53
    c2nd
    cfv
    #
    cle
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
    @52
    cG
    cfv
    #
    c1st
    cfv
    #
    @55
    clt
    wbr
    #
    @55
    @62
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
    @51
    @50
    wph
    @60
    @68
    vz
    cA
    wph
    @55
    cA
    wcel
    #
    wa
    #
    @59
    @67
    vm
    cn
    @71
    @52
    cn
    wcel
    #
    wa
    #
    @56
    @64
    @58
    @66
    @73
    @63
    @54
    clt
    wbr
    #
    @56
    @64
    wph
    @72
    @74
    @70
    wph
    @72
    wa
    #
    @63
    @54
    @19
    c2
    @52
    cexp
    co
    #
    cdiv
    co
    #
    cmin
    co
    #
    @54
    clt
    @75
    @63
    @78
    @57
    @77
    caddc
    co
    #
    cop
    #
    c1st
    cfv
    @78
    @75
    @62
    @80
    c1st
    @72
    @62
    @80
    wceq
    wph
    vn
    @52
    @25
    @80
    cn
    cG
    @16
    @52
    wceq
    #
    @22
    @78
    @24
    @79
    @81
    @18
    @54
    @21
    @77
    cmin
    @81
    @17
    @53
    c1st
    @16
    @52
    cF
    fveq2
    #
    fveq2d
    @81
    @20
    @76
    @19
    cdiv
    @16
    @52
    c2
    cexp
    oveq2
    oveq2d
    #
    oveq12d
    @81
    @23
    @57
    @21
    @77
    caddc
    @81
    @17
    @53
    c2nd
    @82
    fveq2d
    @83
    oveq12d
    opeq12d
    ovollb2.2
    @78
    @79
    opex
    fvmpt
    adantl
    #
    fveq2d
    @78
    @79
    @54
    @77
    cmin
    ovex
    #
    @57
    @77
    caddc
    ovex
    #
    op1st
    syl6eq
    #
    @75
    @54
    @77
    @75
    @54
    cr
    wcel
    #
    @57
    cr
    wcel
    #
    @54
    @57
    cle
    wbr
    #
    wph
    @10
    @72
    @88
    @89
    @90
    w3a
    ovollb2.4
    cF
    @52
    ovolfcl
    sylan
    #
    simp1d
    #
    @75
    @19
    @76
    wph
    @33
    @72
    @34
    adantr
    #
    @75
    @76
    @75
    @35
    @52
    cn0
    wcel
    #
    @76
    cn
    wcel
    2nn
    @72
    @94
    wph
    @52
    nnnn0
    adantl
    c2
    @52
    nnexpcl
    sylancr
    #
    nnrpd
    #
    rpdivcld
    #
    ltsubrpd
    eqbrtrd
    adantlr
    @73
    @63
    cr
    wcel
    #
    @88
    @55
    cr
    wcel
    #
    @74
    @56
    wa
    @64
    wi
    wph
    @72
    @98
    @70
    @75
    @98
    @65
    cr
    wcel
    #
    @63
    @65
    cle
    wbr
    #
    wph
    @15
    @72
    @98
    @100
    @101
    w3a
    @42
    cG
    @52
    ovolfcl
    sylan
    #
    simp1d
    adantlr
    wph
    @72
    @88
    @70
    @92
    adantlr
    @71
    @99
    @72
    wph
    cA
    cr
    @55
    @11
    sselda
    adantr
    #
    @63
    @54
    @55
    ltletr
    syl3anc
    mpand
    @73
    @58
    @57
    @65
    clt
    wbr
    #
    @66
    wph
    @72
    @104
    @70
    @75
    @57
    @79
    @65
    clt
    @75
    @57
    @77
    @75
    @88
    @89
    @90
    @91
    simp2d
    #
    @97
    ltaddrpd
    @75
    @65
    @80
    c2nd
    cfv
    @79
    @75
    @62
    @80
    c2nd
    @84
    fveq2d
    @78
    @79
    @85
    @86
    op2nd
    syl6eq
    #
    breqtrrd
    adantlr
    @73
    @99
    @89
    @100
    @58
    @104
    wa
    @66
    wi
    @103
    wph
    @72
    @89
    @70
    @105
    adantlr
    wph
    @72
    @100
    @70
    @75
    @98
    @100
    @101
    @102
    simp2d
    adantlr
    @55
    @57
    @65
    lelttr
    syl3anc
    mpan2d
    anim12d
    reximdva
    ralimdva
    wph
    @6
    @10
    @51
    @61
    wb
    @11
    ovollb2.4
    vz
    cA
    vm
    cF
    ovolficc
    syl2anc
    wph
    @6
    @15
    @50
    @69
    wb
    @11
    @42
    vz
    cA
    vm
    cG
    ovolfioo
    syl2anc
    3imtr4d
    mpd
    cA
    cT
    cG
    ovollb2.3
    ovollb
    syl2anc
    wph
    @2
    @5
    cle
    wbr
    #
    vy
    cv
    #
    @5
    cle
    wbr
    #
    vy
    @1
    wral
    #
    wph
    @110
    vk
    cv
    #
    cT
    cfv
    #
    @5
    cle
    wbr
    #
    vk
    cn
    wral
    #
    wph
    @113
    vk
    cn
    wph
    @111
    cn
    wcel
    #
    wa
    #
    @112
    @111
    cS
    cfv
    #
    cB
    cB
    c2
    @111
    cexp
    co
    #
    cdiv
    co
    #
    cmin
    co
    #
    caddc
    co
    #
    @5
    cle
    @116
    @112
    @111
    caddc
    @44
    c1
    cseq
    #
    cfv
    #
    @121
    @111
    cT
    @122
    ovollb2.3
    fveq1i
    @116
    c1
    @111
    cfz
    co
    #
    @52
    @43
    cF
    ccom
    #
    cfv
    #
    cB
    @76
    cdiv
    co
    #
    caddc
    co
    #
    vm
    csu
    @124
    @126
    vm
    csu
    #
    @124
    @127
    vm
    csu
    #
    caddc
    co
    @123
    @121
    @116
    @124
    @126
    @127
    vm
    @116
    c1
    @111
    fzfid
    @116
    @52
    @124
    wcel
    #
    wa
    #
    @126
    @132
    @13
    cr
    @126
    rge0ssre
    @116
    cn
    @13
    @125
    wf
    #
    @72
    @126
    @13
    wcel
    @131
    wph
    @133
    @115
    wph
    @10
    @133
    ovollb2.4
    cF
    @125
    @125
    eqid
    #
    ovolfsf
    syl
    adantr
    @52
    @111
    elfznn
    #
    cn
    @13
    @52
    @125
    ffvelrn
    syl2an
    sseldi
    recnd
    #
    wph
    @131
    @127
    cc
    wcel
    #
    @115
    @131
    wph
    @72
    @137
    @135
    @75
    @127
    @75
    cB
    @76
    wph
    cB
    crp
    wcel
    #
    @72
    ovollb2.6
    adantr
    #
    @96
    rpdivcld
    rpcnd
    #
    sylan2
    adantlr
    #
    fsumadd
    @116
    @128
    vm
    @44
    c1
    @111
    wph
    @131
    @52
    @44
    cfv
    #
    @128
    wceq
    #
    @115
    @131
    wph
    @72
    @143
    @135
    @75
    @142
    @65
    @63
    cmin
    co
    #
    @128
    wph
    @15
    @72
    @142
    @144
    wceq
    @42
    cG
    @44
    @52
    @45
    ovolfsval
    sylan
    @75
    @79
    @78
    cmin
    co
    @57
    @77
    @78
    cmin
    co
    #
    caddc
    co
    #
    @144
    @128
    @75
    @57
    @77
    @78
    @75
    @57
    @105
    recnd
    #
    @75
    @77
    @97
    rpcnd
    #
    @75
    @54
    @77
    @75
    @54
    @92
    recnd
    #
    @148
    subcld
    addsubassd
    @75
    @65
    @79
    @63
    @78
    cmin
    @106
    @87
    oveq12d
    @75
    @57
    @54
    cmin
    co
    #
    @127
    caddc
    co
    @57
    @127
    @54
    cmin
    co
    #
    caddc
    co
    @128
    @146
    @75
    @57
    @54
    @127
    @147
    @149
    @140
    subadd23d
    @75
    @126
    @150
    @127
    caddc
    wph
    @10
    @72
    @126
    @150
    wceq
    ovollb2.4
    cF
    @125
    @52
    @134
    ovolfsval
    sylan
    oveq1d
    @75
    @145
    @151
    @57
    caddc
    @75
    @145
    @77
    @77
    caddc
    co
    #
    @54
    cmin
    co
    @151
    @75
    @77
    @54
    @77
    @148
    @149
    @148
    subsub3d
    @75
    @152
    @127
    @54
    cmin
    @75
    @19
    @19
    caddc
    co
    #
    @76
    cdiv
    co
    @152
    @127
    @75
    @19
    @19
    @76
    @75
    @19
    @93
    rpcnd
    #
    @154
    @75
    @76
    @95
    nncnd
    @75
    @76
    @95
    nnne0d
    divdird
    @75
    @153
    cB
    @76
    cdiv
    @75
    cB
    @75
    cB
    @139
    rpcnd
    2halvesd
    oveq1d
    eqtr3d
    oveq1d
    eqtrd
    oveq2d
    3eqtr4d
    3eqtr4d
    eqtrd
    sylan2
    adantlr
    @116
    @111
    cn
    c1
    cuz
    cfv
    wph
    @115
    simpr
    #
    nnuz
    syl6eleq
    #
    @132
    @126
    @127
    @136
    @141
    addcld
    fsumser
    @116
    @129
    @117
    @130
    @120
    caddc
    @116
    @129
    @111
    caddc
    @125
    c1
    cseq
    #
    cfv
    @117
    @116
    @126
    vm
    @125
    c1
    @111
    @132
    @126
    eqidd
    @156
    @136
    fsumser
    @111
    cS
    @157
    ovollb2.1
    fveq1i
    syl6eqr
    @116
    @115
    cB
    cc
    wcel
    @130
    @120
    wceq
    @155
    @116
    cB
    wph
    @138
    @115
    ovollb2.6
    adantr
    #
    rpcnd
    cB
    vm
    @111
    geo2sum
    syl2anc
    oveq12d
    3eqtr3d
    syl5eq
    @116
    @117
    @120
    @4
    cB
    @116
    @13
    cr
    @117
    rge0ssre
    wph
    cn
    @13
    @111
    cS
    wph
    @10
    cn
    @13
    cS
    wf
    #
    ovollb2.4
    cS
    cF
    @125
    @134
    ovollb2.1
    ovolsf
    syl
    #
    ffvelrnda
    sseldi
    @116
    cB
    @119
    @116
    cB
    @158
    rpred
    #
    @116
    @119
    @116
    cB
    @118
    @158
    @116
    @118
    @116
    @35
    @111
    cn0
    wcel
    #
    @118
    cn
    wcel
    2nn
    @115
    @162
    wph
    @111
    nnnn0
    adantl
    c2
    @111
    nnexpcl
    sylancr
    nnrpd
    rpdivcld
    #
    rpred
    resubcld
    #
    wph
    @4
    cr
    wcel
    @115
    ovollb2.7
    adantr
    @161
    @116
    @3
    cxr
    wss
    #
    @117
    @3
    wcel
    #
    @117
    @4
    cle
    wbr
    wph
    @165
    @115
    wph
    @3
    @13
    cxr
    wph
    @159
    @3
    @13
    wss
    @160
    cn
    @13
    cS
    frn
    syl
    @47
    syl6ss
    adantr
    wph
    cS
    cn
    wfn
    #
    @115
    @166
    wph
    @159
    @167
    @160
    cn
    @13
    cS
    ffn
    syl
    cn
    @111
    cS
    fnfvelrn
    sylan
    @3
    @117
    supxrub
    syl2anc
    @116
    @120
    cB
    @164
    @161
    @116
    cB
    @119
    @161
    @163
    ltsubrpd
    ltled
    le2addd
    eqbrtrd
    ralrimiva
    wph
    @14
    cT
    cn
    wfn
    @110
    @114
    wb
    @46
    cn
    @13
    cT
    ffn
    @109
    @113
    vy
    vk
    cn
    cT
    @108
    @112
    @5
    cle
    breq1
    ralrn
    3syl
    mpbird
    wph
    @12
    @5
    cxr
    wcel
    @107
    @110
    wb
    @48
    @49
    vy
    @1
    @5
    supxrleub
    syl2anc
    mpbird
    xrletrd
end
