include "wcel.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wa.mm"
include "cesum.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "cxmu.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "nfel1.mm"
include "nfan.mm"
include "simpl.mm"
include "simplr.mm"
include "cxrs.mm"
include "cress.mm"
include "cgsu.mm"
include "cmg.mm"
include "cmnd.mm"
include "wceq.mm"
include "ctmd.mm"
include "xrge0tmd.mm"
include "tmdmnd.mm"
include "ax-mp.mm"
include "a1i.mm"
include "inss2.mm"
include "simpr.mm"
include "sseldi.mm"
include "xrge0base.mm"
include "eqid.mm"
include "gsumconstf.mm"
include "syl3anc.mm"
include "cn0.mm"
include "hashcl.mm"
include "syl.mm"
include "xrge0mulgnn0.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "esumval.mm"
include "wss.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "cr.mm"
include "wf.mm"
include "csn.mm"
include "cun.mm"
include "nn0ssre.mm"
include "ressxr.mm"
include "sstri.mm"
include "pnfxr.mm"
include "snssi.mm"
include "unssi.mm"
include "cvv.mm"
include "hashf.mm"
include "vex.mm"
include "ffvelrn.mm"
include "mp2an.mm"
include "sselii.mm"
include "iccssxr.mm"
include "adantr.mm"
include "xmulcld.mm"
include "fmptd.mm"
include "frn.mm"
include "hashxrcl.mm"
include "wb.mm"
include "elrnmpt.mm"
include "biimpi.mm"
include "0xr.mm"
include "iccgelb.mm"
include "jca.mm"
include "cdom.mm"
include "inss1.mm"
include "sseli.mm"
include "elpwi.mm"
include "3syl.mm"
include "ssdomg.mm"
include "sylc.mm"
include "hashdomi.mm"
include "xlemul1a.mm"
include "syl31anc.mm"
include "ralrimiva.mm"
include "r19.29r.mm"
include "syl2anr.mm"
include "eqbrtrd.mm"
include "rexlimivw.mm"
include "pwidg.mm"
include "ancri.mm"
include "elin.mm"
include "sylibr.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "ovex.mm"
include "adantl.mm"
include "breq2.mm"
include "wn.mm"
include "crp.mm"
include "c0.mm"
include "0elpw.mm"
include "0fin.mm"
include "mpbir2an.mm"
include "oveq2d.mm"
include "hash0.mm"
include "eqeltri.mm"
include "xmul01.mm"
include "syl6req.mm"
include "elrnmpti.mm"
include "simpllr.mm"
include "ad4antr.mm"
include "breqtrd.mm"
include "cdiv.mm"
include "cn.mm"
include "simp-4r.mm"
include "eqeltrd.mm"
include "nnnn0.mm"
include "hashclb.mm"
include "elind.mm"
include "eqidd.mm"
include "cmul.mm"
include "simp-8r.mm"
include "nnred.mm"
include "simp-5r.mm"
include "ltdivmul2d.mm"
include "mpbid.mm"
include "rpred.mm"
include "rexmul.mm"
include "breqtrrd.mm"
include "ex.mm"
include "rexlimdva.mm"
include "impr.mm"
include "rerpdivcld.mm"
include "arch.mm"
include "ishashinf.mm"
include "ad2antlr.mm"
include "r19.29a.mm"
include "wex.mm"
include "nfielex.mm"
include "snelpwi.mm"
include "snfi.mm"
include "jctir.mm"
include "c1.mm"
include "hashsng.mm"
include "1re.mm"
include "syl6eqel.mm"
include "0lt1.mm"
include "syl5breqr.mm"
include "xmulpnf1.mm"
include "eqtr2d.mm"
include "exlimddv.mm"
include "adantll.mm"
include "ltpnf.mm"
include "w3o.mm"
include "elxrge02.mm"
include "sylib.mm"
include "mpjao3dan.mm"
include "pm2.61dan.mm"
include "supxr2.mm"
include "syl22anc.mm"

theorem esumcst
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cV: class V
  let va: setvar a
  let vl: setvar l
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume esumcst.1: |- F/_ k A
  assume esumcst.2: |- F/_ k B

  disjoint V k
  disjoint a l
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint l n
  disjoint l x
  disjoint l y
  disjoint l z
  disjoint A l
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B a
  disjoint B l
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint a k
  disjoint V a
  disjoint k l
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint V l
  disjoint V n
  disjoint V x
  disjoint V y
  assert |- ( ( A e. V /\ B e. ( 0 [,] +oo ) ) -> sum* k e. A B = ( ( # ` A ) *e B ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    wa
    #
    cA
    cB
    vk
    cesum
    vx
    cA
    cpw
    #
    cfn
    cin
    #
    vx
    cv
    #
    chash
    cfv
    #
    cB
    cxmu
    co
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cA
    chash
    cfv
    #
    cB
    cxmu
    co
    #
    @3
    vx
    cA
    cB
    @8
    vk
    cV
    @0
    @2
    vk
    vk
    cA
    cV
    esumcst.1
    nfel1
    vk
    cB
    @1
    esumcst.2
    nfel1
    nfan
    esumcst.1
    @0
    @2
    simpl
    #
    @0
    @2
    vk
    cv
    cA
    wcel
    simplr
    @3
    @6
    @5
    wcel
    #
    wa
    #
    cxrs
    @1
    cress
    co
    #
    vk
    @6
    cB
    cmpt
    cgsu
    co
    #
    @7
    cB
    @17
    cmg
    cfv
    #
    co
    #
    @8
    @16
    @17
    cmnd
    wcel
    #
    @6
    cfn
    wcel
    #
    @2
    @18
    @20
    wceq
    @21
    @16
    @17
    ctmd
    wcel
    @21
    xrge0tmd
    @17
    tmdmnd
    ax-mp
    a1i
    @16
    @5
    cfn
    @6
    @4
    cfn
    inss2
    @3
    @15
    simpr
    #
    sseldi
    #
    @0
    @2
    @15
    simplr
    #
    @6
    @1
    @19
    vk
    @17
    cB
    esumcst.2
    xrge0base
    @19
    eqid
    gsumconstf
    syl3anc
    @16
    @7
    cn0
    wcel
    #
    @2
    @20
    @8
    wceq
    @16
    @22
    @26
    @24
    @6
    hashcl
    syl
    @25
    @7
    cB
    xrge0mulgnn0
    syl2anc
    eqtrd
    esumval
    @3
    @10
    cxr
    wss
    #
    @13
    cxr
    wcel
    vy
    cv
    #
    @13
    cle
    wbr
    #
    vy
    @10
    wral
    @28
    @13
    clt
    wbr
    #
    @28
    vz
    cv
    #
    clt
    wbr
    #
    vz
    @10
    wrex
    #
    wi
    #
    vy
    cr
    wral
    @11
    @13
    wceq
    @3
    @5
    cxr
    @9
    wf
    @27
    @3
    vx
    @5
    @8
    cxr
    @9
    @16
    @7
    cB
    @7
    cxr
    wcel
    #
    @16
    cn0
    cpnf
    csn
    #
    cun
    #
    cxr
    @7
    cn0
    @36
    cxr
    cn0
    cr
    cxr
    nn0ssre
    ressxr
    sstri
    cpnf
    cxr
    wcel
    #
    @36
    cxr
    wss
    pnfxr
    cpnf
    cxr
    snssi
    ax-mp
    unssi
    cvv
    @37
    chash
    wf
    @6
    cvv
    wcel
    @7
    @37
    wcel
    hashf
    vx
    vex
    cvv
    @37
    @6
    chash
    ffvelrn
    mp2an
    sselii
    a1i
    #
    @3
    cB
    cxr
    wcel
    #
    @15
    @3
    @1
    cxr
    cB
    cc0
    cpnf
    iccssxr
    @0
    @2
    simpr
    sseldi
    #
    adantr
    #
    xmulcld
    @9
    eqid
    #
    fmptd
    @5
    cxr
    @9
    frn
    syl
    @3
    @12
    cB
    @0
    @12
    cxr
    wcel
    #
    @2
    cA
    cV
    hashxrcl
    adantr
    #
    @41
    xmulcld
    @3
    @29
    vy
    @10
    @3
    @28
    @10
    wcel
    #
    wa
    @28
    @8
    wceq
    #
    @8
    @13
    cle
    wbr
    #
    wa
    #
    vx
    @5
    wrex
    #
    @29
    @46
    @47
    vx
    @5
    wrex
    #
    @48
    vx
    @5
    wral
    @50
    @3
    @46
    @51
    @28
    cvv
    wcel
    @46
    @51
    wb
    vy
    vex
    vx
    @5
    @8
    @28
    @9
    cvv
    @43
    elrnmpt
    ax-mp
    biimpi
    @3
    @48
    vx
    @5
    @16
    @35
    @44
    @40
    cc0
    cB
    cle
    wbr
    #
    wa
    @7
    @12
    cle
    wbr
    #
    @48
    @39
    @3
    @44
    @15
    @45
    adantr
    @16
    @40
    @52
    @42
    @16
    cc0
    cxr
    wcel
    #
    @38
    @2
    @52
    @54
    @16
    0xr
    a1i
    @38
    @16
    pnfxr
    a1i
    @25
    cc0
    cpnf
    cB
    iccgelb
    syl3anc
    jca
    @16
    @6
    cA
    cdom
    wbr
    #
    @53
    @16
    @0
    @6
    cA
    wss
    #
    @55
    @3
    @0
    @15
    @14
    adantr
    @16
    @15
    @6
    @4
    wcel
    @56
    @23
    @5
    @4
    @6
    @4
    cfn
    inss1
    sseli
    @6
    cA
    elpwi
    3syl
    @6
    cA
    cV
    ssdomg
    sylc
    @6
    cA
    hashdomi
    syl
    @7
    @12
    cB
    xlemul1a
    syl31anc
    ralrimiva
    @47
    @48
    vx
    @5
    r19.29r
    syl2anr
    @49
    @29
    vx
    @5
    @49
    @28
    @8
    @13
    cle
    @47
    @48
    simpl
    @47
    @48
    simpr
    eqbrtrd
    rexlimivw
    syl
    ralrimiva
    @3
    @34
    vy
    cr
    @3
    @28
    cr
    wcel
    #
    wa
    #
    @30
    @33
    @58
    @30
    wa
    #
    cA
    cfn
    wcel
    #
    @33
    @59
    @60
    wa
    @13
    @10
    wcel
    #
    @30
    @33
    @60
    @61
    @59
    @60
    cA
    @5
    wcel
    #
    @61
    @60
    cA
    @4
    wcel
    #
    @60
    wa
    @62
    @60
    @63
    cA
    cfn
    pwidg
    ancri
    cA
    @4
    cfn
    elin
    sylibr
    @62
    @13
    @8
    wceq
    #
    vx
    @5
    wrex
    #
    @61
    @62
    @13
    @13
    wceq
    #
    @65
    @13
    eqid
    @64
    @66
    vx
    cA
    @5
    @6
    cA
    wceq
    #
    @8
    @13
    @13
    @67
    @7
    @12
    cB
    cxmu
    @6
    cA
    chash
    fveq2
    oveq1d
    eqeq2d
    rspcev
    mpan2
    @13
    cvv
    wcel
    @61
    @65
    wb
    @12
    cB
    cxmu
    ovex
    vx
    @5
    @8
    @13
    @9
    cvv
    @43
    elrnmpt
    ax-mp
    sylibr
    syl
    adantl
    @58
    @30
    @60
    simplr
    @32
    @30
    vz
    @13
    @10
    @31
    @13
    @28
    clt
    breq2
    rspcev
    syl2anc
    @59
    @60
    wn
    #
    wa
    #
    cB
    cc0
    wceq
    #
    @33
    cB
    crp
    wcel
    #
    cB
    cpnf
    wceq
    #
    @69
    @70
    wa
    #
    cc0
    @10
    wcel
    #
    @28
    cc0
    clt
    wbr
    #
    @33
    @73
    cc0
    @8
    wceq
    #
    vx
    @5
    wrex
    #
    @74
    @73
    c0
    @5
    wcel
    #
    cc0
    c0
    chash
    cfv
    #
    cB
    cxmu
    co
    #
    wceq
    #
    @77
    @78
    @73
    @78
    c0
    @4
    wcel
    c0
    cfn
    wcel
    cA
    0elpw
    0fin
    c0
    @4
    cfn
    elin
    mpbir2an
    a1i
    @73
    @80
    @79
    cc0
    cxmu
    co
    #
    cc0
    @73
    cB
    cc0
    @79
    cxmu
    @69
    @70
    simpr
    #
    oveq2d
    @79
    cxr
    wcel
    @82
    cc0
    wceq
    @79
    cc0
    cxr
    hash0
    0xr
    eqeltri
    @79
    xmul01
    ax-mp
    syl6req
    @76
    @81
    vx
    c0
    @5
    @6
    c0
    wceq
    #
    @8
    @80
    cc0
    @84
    @7
    @79
    cB
    cxmu
    @6
    c0
    chash
    fveq2
    oveq1d
    eqeq2d
    rspcev
    syl2anc
    vx
    @5
    @8
    cc0
    @9
    @43
    @7
    cB
    cxmu
    ovex
    #
    elrnmpti
    sylibr
    @73
    @28
    @13
    cc0
    clt
    @58
    @30
    @68
    @70
    simpllr
    @73
    @13
    @12
    cc0
    cxmu
    co
    #
    cc0
    @73
    cB
    cc0
    @12
    cxmu
    @83
    oveq2d
    @73
    @44
    @86
    cc0
    wceq
    @3
    @44
    @57
    @30
    @68
    @70
    @45
    ad4antr
    @12
    xmul01
    syl
    eqtrd
    breqtrd
    @32
    @75
    vz
    cc0
    @10
    @31
    cc0
    @28
    clt
    breq2
    rspcev
    syl2anc
    @69
    @71
    wa
    #
    @28
    cB
    cdiv
    co
    #
    vn
    cv
    #
    clt
    wbr
    #
    va
    cv
    #
    chash
    cfv
    #
    @89
    wceq
    #
    va
    @4
    wrex
    #
    wa
    #
    @33
    vn
    cn
    @87
    @89
    cn
    wcel
    #
    wa
    #
    @90
    @94
    @33
    @97
    @90
    wa
    #
    @93
    @33
    va
    @4
    @98
    @91
    @4
    wcel
    #
    wa
    #
    @93
    @33
    @100
    @93
    wa
    #
    @92
    cB
    cxmu
    co
    #
    @10
    wcel
    #
    @28
    @102
    clt
    wbr
    #
    @33
    @101
    @102
    @8
    wceq
    #
    vx
    @5
    wrex
    #
    @103
    @101
    @91
    @5
    wcel
    @102
    @102
    wceq
    #
    @106
    @101
    @4
    cfn
    @91
    @98
    @99
    @93
    simplr
    @101
    @92
    cn
    wcel
    #
    @91
    cfn
    wcel
    #
    @101
    @92
    @89
    cn
    @100
    @93
    simpr
    #
    @87
    @96
    @90
    @99
    @93
    simp-4r
    #
    eqeltrd
    @108
    @92
    cn0
    wcel
    #
    @109
    @92
    nnnn0
    @91
    cvv
    wcel
    @109
    @112
    wb
    va
    vex
    @91
    cvv
    hashclb
    ax-mp
    sylibr
    syl
    elind
    @101
    @102
    eqidd
    @105
    @107
    vx
    @91
    @5
    @6
    @91
    wceq
    #
    @8
    @102
    @102
    @113
    @7
    @92
    cB
    cxmu
    @6
    @91
    chash
    fveq2
    oveq1d
    eqeq2d
    rspcev
    syl2anc
    vx
    @5
    @8
    @102
    @9
    @43
    @85
    elrnmpti
    sylibr
    @101
    @28
    @89
    cB
    cmul
    co
    #
    @102
    clt
    @101
    @90
    @28
    @114
    clt
    wbr
    @97
    @90
    @99
    @93
    simpllr
    @101
    @28
    @89
    cB
    @3
    @57
    @30
    @68
    @71
    @96
    @90
    @99
    @93
    simp-8r
    @101
    @89
    @111
    nnred
    #
    @69
    @71
    @96
    @90
    @99
    @93
    simp-5r
    #
    ltdivmul2d
    mpbid
    @101
    @102
    @89
    cB
    cxmu
    co
    #
    @114
    @101
    @92
    @89
    cB
    cxmu
    @110
    oveq1d
    @101
    @89
    cr
    wcel
    cB
    cr
    wcel
    @117
    @114
    wceq
    @115
    @101
    cB
    @116
    rpred
    @89
    cB
    rexmul
    syl2anc
    eqtrd
    breqtrrd
    @32
    @104
    vz
    @102
    @10
    @31
    @102
    @28
    clt
    breq2
    rspcev
    syl2anc
    ex
    rexlimdva
    impr
    @87
    @90
    vn
    cn
    wrex
    #
    @94
    vn
    cn
    wral
    #
    @95
    vn
    cn
    wrex
    @87
    @88
    cr
    wcel
    @118
    @87
    @28
    cB
    @3
    @57
    @30
    @68
    @71
    simp-4r
    @69
    @71
    simpr
    rerpdivcld
    @88
    vn
    arch
    syl
    @68
    @119
    @59
    @71
    va
    cA
    vn
    ishashinf
    ad2antlr
    @90
    @94
    vn
    cn
    r19.29r
    syl2anc
    r19.29a
    @69
    @72
    wa
    #
    cpnf
    @10
    wcel
    #
    @28
    cpnf
    clt
    wbr
    #
    @33
    @120
    cpnf
    @8
    wceq
    #
    vx
    @5
    wrex
    #
    @121
    @68
    @72
    @124
    @59
    @68
    @72
    wa
    #
    vl
    cv
    #
    cA
    wcel
    #
    @124
    vl
    @68
    @127
    vl
    wex
    @72
    vl
    cA
    nfielex
    adantr
    @125
    @127
    wa
    #
    @126
    csn
    #
    @5
    wcel
    #
    cpnf
    @129
    chash
    cfv
    #
    cB
    cxmu
    co
    #
    wceq
    #
    @124
    @127
    @130
    @125
    @127
    @129
    @4
    wcel
    #
    @129
    cfn
    wcel
    #
    wa
    @130
    @127
    @134
    @135
    @126
    cA
    snelpwi
    @126
    snfi
    jctir
    @129
    @4
    cfn
    elin
    sylibr
    adantl
    @128
    @132
    @131
    cpnf
    cxmu
    co
    #
    cpnf
    @128
    cB
    cpnf
    @131
    cxmu
    @68
    @72
    @127
    simplr
    oveq2d
    @127
    @136
    cpnf
    wceq
    #
    @125
    @127
    @131
    cxr
    wcel
    cc0
    @131
    clt
    wbr
    @137
    @127
    @131
    c1
    cxr
    @126
    cA
    hashsng
    #
    cr
    cxr
    c1
    ressxr
    1re
    sselii
    syl6eqel
    @127
    cc0
    c1
    @131
    clt
    0lt1
    @138
    syl5breqr
    @131
    xmulpnf1
    syl2anc
    adantl
    eqtr2d
    @123
    @133
    vx
    @129
    @5
    @6
    @129
    wceq
    #
    @8
    @132
    cpnf
    @139
    @7
    @131
    cB
    cxmu
    @6
    @129
    chash
    fveq2
    oveq1d
    eqeq2d
    rspcev
    syl2anc
    exlimddv
    adantll
    vx
    @5
    @8
    cpnf
    @9
    @43
    @85
    elrnmpti
    sylibr
    @120
    @57
    @122
    @3
    @57
    @30
    @68
    @72
    simp-4r
    @28
    ltpnf
    syl
    @32
    @122
    vz
    cpnf
    @10
    @31
    cpnf
    @28
    clt
    breq2
    rspcev
    syl2anc
    @69
    @2
    @70
    @71
    @72
    w3o
    @0
    @2
    @57
    @30
    @68
    simp-4r
    cB
    elxrge02
    sylib
    mpjao3dan
    pm2.61dan
    ex
    ralrimiva
    vy
    vz
    @10
    @13
    supxr2
    syl22anc
    eqtrd
end
