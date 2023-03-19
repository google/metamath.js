include "cr.mm"
include "crn.mm"
include "c1st.mm"
include "ccom.mm"
include "clt.mm"
include "csup.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wcel.mm"
include "c1.mm"
include "ruclem11.mm"
include "simp1d.mm"
include "simp2d.mm"
include "1re.mm"
include "simp3d.mm"
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "sylancr.mm"
include "suprcl.mm"
include "syl3anc.mm"
include "syl5eqel.mm"
include "cfv.mm"
include "cn.mm"
include "wa.mm"
include "wo.mm"
include "c2nd.mm"
include "cmin.mm"
include "co.mm"
include "cop.mm"
include "wf.mm"
include "adantr.mm"
include "cxp.mm"
include "caddc.mm"
include "c2.mm"
include "cdiv.mm"
include "cif.mm"
include "csb.mm"
include "cmpt2.mm"
include "cn0.mm"
include "ruclem6.mm"
include "nnm1nn0.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "xp1st.mm"
include "syl.mm"
include "xp2nd.mm"
include "ffvelrnda.mm"
include "eqid.mm"
include "ruclem8.mm"
include "sylan2.mm"
include "ruclem3.mm"
include "ruclem7.mm"
include "cc.mm"
include "nncn.mm"
include "adantl.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "fveq2d.mm"
include "1st2nd2.mm"
include "oveq12d.mm"
include "3eqtr3d.mm"
include "breq2d.mm"
include "breq1d.mm"
include "orbi12d.mm"
include "mpbird.mm"
include "nnnn0.mm"
include "fvco3.mm"
include "wfn.mm"
include "1stcof.mm"
include "ffn.mm"
include "3syl.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "suprub.mm"
include "syl31anc.mm"
include "syl6breqr.mm"
include "wi.mm"
include "ltletr.mm"
include "mpan2d.mm"
include "sylan.mm"
include "simpr.mm"
include "ruclem10.mm"
include "ltled.mm"
include "eqbrtrd.mm"
include "ralrimiva.mm"
include "wb.mm"
include "breq1.mm"
include "ralrn.mm"
include "suprleub.mm"
include "syl5eqbr.mm"
include "lelttr.mm"
include "mpand.mm"
include "orim12d.mm"
include "mpd.mm"
include "lttri2d.mm"
include "neneqd.mm"
include "nrexdv.mm"
include "risset.mm"
include "eqeq1.mm"
include "rexrn.mm"
include "syl5bb.mm"
include "mtbird.mm"
include "eldifd.mm"

theorem ruclem12
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let cS: class S
  let vm: setvar m
  let cF: class F
  let cG: class G
  let vw: setvar w
  let cA: class A
  let cB: class B
  let vz: setvar z
  let vn: setvar n
  let vk: setvar k
  let cM: class M
  let cN: class N
  assume ruc.1: |- ( ph -> F : NN --> RR )
  assume ruc.2: |- ( ph -> D = ( x e. ( RR X. RR ) , y e. RR |-> [_ ( ( ( 1st ` x ) + ( 2nd ` x ) ) / 2 ) / m ]_ if ( m < y , <. ( 1st ` x ) , m >. , <. ( ( m + ( 2nd ` x ) ) / 2 ) , ( 2nd ` x ) >. ) ) )
  assume ruc.4: |- C = ( { <. 0 , <. 0 , 1 >. >. } u. F )
  assume ruc.5: |- G = seq 0 ( D , C )
  assume ruc.6: |- S = sup ( ran ( 1st o. G ) , RR , < )

  disjoint m x
  disjoint m y
  disjoint x y
  disjoint F m
  disjoint F x
  disjoint F y
  disjoint G m
  disjoint G x
  disjoint G y
  disjoint m w
  disjoint w x
  disjoint w y
  disjoint A m
  disjoint A x
  disjoint A y
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint w z
  disjoint C w
  disjoint C z
  disjoint m n
  disjoint m z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint G k
  disjoint G n
  disjoint G z
  disjoint M k
  disjoint M m
  disjoint M n
  disjoint M x
  disjoint M y
  disjoint N k
  disjoint N m
  disjoint N x
  disjoint N y
  disjoint k w
  disjoint k ph
  disjoint n w
  disjoint n ph
  disjoint ph w
  disjoint ph z
  disjoint D w
  disjoint D z
  disjoint S n
  disjoint S z
  assert |- ( ph -> S e. ( RR \ ran F ) )

  proof
    wph
    cS
    cr
    cF
    crn
    #
    wph
    cS
    c1st
    cG
    ccom
    #
    crn
    #
    cr
    clt
    csup
    #
    cr
    ruc.6
    wph
    @2
    cr
    wss
    #
    @2
    c0
    wne
    #
    vz
    cv
    #
    vn
    cv
    #
    cle
    wbr
    #
    vz
    @2
    wral
    #
    vn
    cr
    wrex
    #
    @3
    cr
    wcel
    wph
    @4
    @5
    @6
    c1
    cle
    wbr
    #
    vz
    @2
    wral
    #
    wph
    vx
    vy
    vz
    cC
    cD
    vm
    cF
    cG
    ruc.1
    ruc.2
    ruc.4
    ruc.5
    ruclem11
    #
    simp1d
    #
    wph
    @4
    @5
    @12
    @13
    simp2d
    #
    wph
    c1
    cr
    wcel
    @12
    @10
    1re
    wph
    @4
    @5
    @12
    @13
    simp3d
    @9
    @12
    vn
    c1
    cr
    @7
    c1
    wceq
    @8
    @11
    vz
    @2
    @7
    c1
    @6
    cle
    breq2
    ralbidv
    rspcev
    sylancr
    #
    vn
    vz
    @2
    suprcl
    syl3anc
    syl5eqel
    #
    wph
    cS
    @0
    wcel
    #
    @7
    cF
    cfv
    #
    cS
    wceq
    #
    vn
    cn
    wrex
    #
    wph
    @20
    vn
    cn
    wph
    @7
    cn
    wcel
    #
    wa
    #
    @19
    cS
    @23
    @19
    cS
    wne
    @19
    cS
    clt
    wbr
    #
    cS
    @19
    clt
    wbr
    #
    wo
    #
    @23
    @19
    @7
    cG
    cfv
    #
    c1st
    cfv
    #
    clt
    wbr
    #
    @27
    c2nd
    cfv
    #
    @19
    clt
    wbr
    #
    wo
    #
    @26
    @23
    @32
    @19
    @7
    c1
    cmin
    co
    #
    cG
    cfv
    #
    c1st
    cfv
    #
    @34
    c2nd
    cfv
    #
    cop
    #
    @19
    cD
    co
    #
    c1st
    cfv
    #
    clt
    wbr
    #
    @38
    c2nd
    cfv
    #
    @19
    clt
    wbr
    #
    wo
    @23
    vx
    vy
    @35
    @36
    cD
    vm
    cF
    @19
    @39
    @41
    wph
    cn
    cr
    cF
    wf
    #
    @22
    ruc.1
    adantr
    #
    wph
    cD
    vx
    vy
    cr
    cr
    cxp
    #
    cr
    vm
    vx
    cv
    #
    c1st
    cfv
    #
    @46
    c2nd
    cfv
    #
    caddc
    co
    c2
    cdiv
    co
    vm
    cv
    #
    vy
    cv
    clt
    wbr
    @47
    @49
    cop
    @49
    @48
    caddc
    co
    c2
    cdiv
    co
    @48
    cop
    cif
    csb
    cmpt2
    wceq
    #
    @22
    ruc.2
    adantr
    #
    @23
    @34
    @45
    wcel
    #
    @35
    cr
    wcel
    wph
    cn0
    @45
    cG
    wf
    #
    @33
    cn0
    wcel
    #
    @52
    @22
    wph
    vx
    vy
    cC
    cD
    vm
    cF
    cG
    ruc.1
    ruc.2
    ruc.4
    ruc.5
    ruclem6
    #
    @7
    nnm1nn0
    #
    cn0
    @45
    @33
    cG
    ffvelrn
    syl2an
    #
    @34
    cr
    cr
    xp1st
    syl
    @23
    @52
    @36
    cr
    wcel
    @57
    @34
    cr
    cr
    xp2nd
    syl
    wph
    cn
    cr
    @7
    cF
    ruc.1
    ffvelrnda
    #
    @39
    eqid
    @41
    eqid
    @22
    wph
    @54
    @35
    @36
    clt
    wbr
    @56
    wph
    vx
    vy
    cC
    cD
    vm
    cF
    cG
    @33
    ruc.1
    ruc.2
    ruc.4
    ruc.5
    ruclem8
    sylan2
    ruclem3
    @23
    @29
    @40
    @31
    @42
    @23
    @28
    @39
    @19
    clt
    @23
    @27
    @38
    c1st
    @23
    @33
    c1
    caddc
    co
    #
    cG
    cfv
    #
    @34
    @59
    cF
    cfv
    #
    cD
    co
    #
    @27
    @38
    @22
    wph
    @54
    @60
    @62
    wceq
    @56
    wph
    vx
    vy
    cC
    cD
    vm
    cF
    cG
    @33
    ruc.1
    ruc.2
    ruc.4
    ruc.5
    ruclem7
    sylan2
    @23
    @59
    @7
    cG
    @23
    @7
    cc
    wcel
    #
    c1
    cc
    wcel
    @59
    @7
    wceq
    @22
    @63
    wph
    @7
    nncn
    adantl
    ax-1cn
    @7
    c1
    npcan
    sylancl
    #
    fveq2d
    @23
    @34
    @37
    @61
    @19
    cD
    @23
    @52
    @34
    @37
    wceq
    @57
    @34
    cr
    cr
    1st2nd2
    syl
    @23
    @59
    @7
    cF
    @64
    fveq2d
    oveq12d
    3eqtr3d
    #
    fveq2d
    breq2d
    @23
    @30
    @41
    @19
    clt
    @23
    @27
    @38
    c2nd
    @65
    fveq2d
    breq1d
    orbi12d
    mpbird
    @23
    @29
    @24
    @31
    @25
    @23
    @29
    @28
    cS
    cle
    wbr
    #
    @24
    @23
    @28
    @3
    cS
    cle
    @23
    @4
    @5
    @10
    @28
    @2
    wcel
    @28
    @3
    cle
    wbr
    wph
    @4
    @22
    @14
    adantr
    #
    wph
    @5
    @22
    @15
    adantr
    #
    wph
    @10
    @22
    @16
    adantr
    #
    @23
    @7
    @1
    cfv
    #
    @28
    @2
    wph
    @53
    @7
    cn0
    wcel
    #
    @70
    @28
    wceq
    @22
    @55
    @7
    nnnn0
    #
    cn0
    @45
    @7
    c1st
    cG
    fvco3
    syl2an
    @23
    @1
    cn0
    wfn
    #
    @71
    @70
    @2
    wcel
    @23
    @53
    cn0
    cr
    @1
    wf
    @73
    wph
    @53
    @22
    @55
    adantr
    #
    cn0
    cr
    cr
    cG
    1stcof
    cn0
    cr
    @1
    ffn
    3syl
    #
    @22
    @71
    wph
    @72
    adantl
    #
    cn0
    @7
    @1
    fnfvelrn
    syl2anc
    eqeltrrd
    vn
    vz
    @2
    @28
    suprub
    syl31anc
    ruc.6
    syl6breqr
    @23
    @19
    cr
    wcel
    #
    @28
    cr
    wcel
    #
    cS
    cr
    wcel
    #
    @29
    @66
    wa
    @24
    wi
    @58
    @23
    @27
    @45
    wcel
    #
    @78
    wph
    @53
    @71
    @80
    @22
    @55
    @72
    cn0
    @45
    @7
    cG
    ffvelrn
    syl2an
    #
    @27
    cr
    cr
    xp1st
    syl
    wph
    @79
    @22
    @17
    adantr
    #
    @19
    @28
    cS
    ltletr
    syl3anc
    mpan2d
    @23
    cS
    @30
    cle
    wbr
    #
    @31
    @25
    @23
    cS
    @3
    @30
    cle
    ruc.6
    @23
    @3
    @30
    cle
    wbr
    #
    @6
    @30
    cle
    wbr
    #
    vz
    @2
    wral
    #
    @23
    @86
    vk
    cv
    #
    @1
    cfv
    #
    @30
    cle
    wbr
    #
    vk
    cn0
    wral
    #
    @23
    @89
    vk
    cn0
    @23
    @87
    cn0
    wcel
    #
    wa
    #
    @88
    @87
    cG
    cfv
    #
    c1st
    cfv
    #
    @30
    cle
    @23
    @53
    @91
    @88
    @94
    wceq
    @74
    cn0
    @45
    @87
    c1st
    cG
    fvco3
    sylan
    @92
    @94
    @30
    @92
    @93
    @45
    wcel
    @94
    cr
    wcel
    @23
    cn0
    @45
    @87
    cG
    @74
    ffvelrnda
    @93
    cr
    cr
    xp1st
    syl
    @23
    @30
    cr
    wcel
    #
    @91
    @23
    @80
    @95
    @81
    @27
    cr
    cr
    xp2nd
    syl
    #
    adantr
    @92
    vx
    vy
    cC
    cD
    vm
    cF
    cG
    @87
    @7
    @23
    @43
    @91
    @44
    adantr
    @23
    @50
    @91
    @51
    adantr
    ruc.4
    ruc.5
    @23
    @91
    simpr
    @23
    @71
    @91
    @76
    adantr
    ruclem10
    ltled
    eqbrtrd
    ralrimiva
    @23
    @73
    @86
    @90
    wb
    @75
    @85
    @89
    vz
    vk
    cn0
    @1
    @6
    @88
    @30
    cle
    breq1
    ralrn
    syl
    mpbird
    @23
    @4
    @5
    @10
    @95
    @84
    @86
    wb
    @67
    @68
    @69
    @96
    vn
    vz
    vz
    @2
    @30
    suprleub
    syl31anc
    mpbird
    syl5eqbr
    @23
    @79
    @95
    @77
    @83
    @31
    wa
    @25
    wi
    @82
    @96
    @58
    cS
    @30
    @19
    lelttr
    syl3anc
    mpand
    orim12d
    mpd
    @23
    @19
    cS
    @58
    @82
    lttri2d
    mpbird
    neneqd
    nrexdv
    @18
    @6
    cS
    wceq
    #
    vz
    @0
    wrex
    #
    wph
    @21
    vz
    cS
    @0
    risset
    wph
    @43
    cF
    cn
    wfn
    @98
    @21
    wb
    ruc.1
    cn
    cr
    cF
    ffn
    @97
    @20
    vz
    vn
    cn
    cF
    @6
    @19
    cS
    eqeq1
    rexrn
    3syl
    syl5bb
    mtbird
    eldifd
end
