include "cv.mm"
include "c1.mm"
include "wne.mm"
include "cfv.mm"
include "wi.mm"
include "c2.mm"
include "wa.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "wral.mm"
include "c3.mm"
include "wceq.mm"
include "w3a.mm"
include "3wlkdlem3.mm"
include "simpr1l.mm"
include "wb.mm"
include "simpl.mm"
include "adantr.mm"
include "simpr.mm"
include "neeq12d.mm"
include "mpbird.mm"
include "a1d.mm"
include "simpr1r.mm"
include "adantl.mm"
include "jca.mm"
include "eqid.mm"
include "2a1i.mm"
include "necon3d.mm"
include "simpr2l.mm"
include "necomd.mm"
include "simpr2r.mm"
include "simp3.mm"
include "ancoms.mm"
include "jca31.mm"
include "syl2anc.mm"
include "cpr.mm"
include "cun.mm"
include "c4.mm"
include "cs4.mm"
include "fveq2i.mm"
include "s4len.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "fzo0to42pr.mm"
include "raleqi.mm"
include "ralunb.mm"
include "c0ex.mm"
include "1ex.mm"
include "neeq1.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "imbi12d.mm"
include "anbi12d.mm"
include "ralpr.mm"
include "2ex.mm"
include "3ex.mm"
include "anbi12i.mm"
include "3bitri.mm"
include "sylibr.mm"
include "cs3.mm"
include "s3len.mm"
include "fzo13pr.mm"
include "neeq2.mm"
include "neeq2d.mm"
include "bitri.mm"
include "ralbii.mm"

theorem 3pthdlem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cK: class K
  let cL: class L
  let cV: class V
  assume 3wlkd.p: |- P = <" A B C D ">
  assume 3wlkd.f: |- F = <" J K L ">
  assume 3wlkd.s: |- ( ph -> ( ( A e. V /\ B e. V ) /\ ( C e. V /\ D e. V ) ) )
  assume 3wlkd.n: |- ( ph -> ( ( A =/= B /\ A =/= C ) /\ ( B =/= C /\ B =/= D ) /\ C =/= D ) )

  disjoint A k
  disjoint B k
  disjoint C k
  disjoint D k
  disjoint J k
  disjoint K k
  disjoint L k
  disjoint V k
  disjoint F k
  disjoint P k
  disjoint F j
  disjoint j k
  disjoint P j
  assert |- ( ph -> A. k e. ( 0 ..^ ( # ` P ) ) A. j e. ( 1 ..^ ( # ` F ) ) ( k =/= j -> ( P ` k ) =/= ( P ` j ) ) )

  proof
    wph
    vk
    cv
    #
    c1
    wne
    #
    @0
    cP
    cfv
    #
    c1
    cP
    cfv
    #
    wne
    #
    wi
    #
    @0
    c2
    wne
    #
    @2
    c2
    cP
    cfv
    #
    wne
    #
    wi
    #
    wa
    #
    vk
    cc0
    cP
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    @0
    vj
    cv
    #
    wne
    #
    @2
    @14
    cP
    cfv
    #
    wne
    #
    wi
    #
    vj
    c1
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    vk
    @12
    wral
    wph
    cc0
    c1
    wne
    #
    cc0
    cP
    cfv
    #
    @3
    wne
    #
    wi
    #
    cc0
    c2
    wne
    #
    @23
    @7
    wne
    #
    wi
    #
    wa
    #
    c1
    c1
    wne
    #
    @3
    @3
    wne
    #
    wi
    #
    c1
    c2
    wne
    #
    @3
    @7
    wne
    #
    wi
    #
    wa
    #
    wa
    #
    c2
    c1
    wne
    #
    @7
    @3
    wne
    #
    wi
    #
    c2
    c2
    wne
    #
    @7
    @7
    wne
    #
    wi
    #
    wa
    #
    c3
    c1
    wne
    #
    c3
    cP
    cfv
    #
    @3
    wne
    #
    wi
    #
    c3
    c2
    wne
    #
    @46
    @7
    wne
    #
    wi
    #
    wa
    #
    wa
    #
    wa
    #
    @13
    wph
    @23
    cA
    wceq
    #
    @3
    cB
    wceq
    #
    wa
    #
    @7
    cC
    wceq
    #
    @46
    cD
    wceq
    #
    wa
    #
    wa
    #
    cA
    cB
    wne
    #
    cA
    cC
    wne
    #
    wa
    #
    cB
    cC
    wne
    #
    cB
    cD
    wne
    #
    wa
    #
    cC
    cD
    wne
    #
    w3a
    #
    @54
    wph
    cA
    cB
    cC
    cD
    cP
    cF
    cJ
    cK
    cL
    cV
    3wlkd.p
    3wlkd.f
    3wlkd.s
    3wlkdlem3
    3wlkd.n
    @61
    @69
    wa
    #
    @29
    @36
    @53
    @70
    @25
    @28
    @70
    @24
    @22
    @70
    @24
    @62
    @62
    @63
    @67
    @68
    @61
    simpr1l
    @61
    @24
    @62
    wb
    @69
    @61
    @23
    cA
    @3
    cB
    @57
    @55
    @60
    @55
    @56
    simpl
    adantr
    #
    @57
    @56
    @60
    @55
    @56
    simpr
    adantr
    #
    neeq12d
    adantr
    mpbird
    a1d
    @70
    @27
    @26
    @70
    @27
    @63
    @62
    @63
    @67
    @68
    @61
    simpr1r
    @61
    @27
    @63
    wb
    @69
    @61
    @23
    cA
    @7
    cC
    @71
    @60
    @58
    @57
    @58
    @59
    simpl
    adantl
    #
    neeq12d
    adantr
    mpbird
    a1d
    jca
    @70
    @32
    @35
    @70
    @3
    @3
    c1
    c1
    c1
    c1
    wceq
    @70
    @3
    @3
    wceq
    c1
    eqid
    2a1i
    necon3d
    @70
    @34
    @33
    @70
    @34
    @65
    @65
    @66
    @64
    @68
    @61
    simpr2l
    @61
    @34
    @65
    wb
    @69
    @61
    @3
    cB
    @7
    cC
    @72
    @73
    neeq12d
    adantr
    mpbird
    #
    a1d
    jca
    @70
    @40
    @43
    @52
    @70
    @39
    @38
    @70
    @3
    @7
    @74
    necomd
    a1d
    @70
    @7
    @7
    c2
    c2
    c2
    c2
    wceq
    @70
    @7
    @7
    wceq
    c2
    eqid
    2a1i
    necon3d
    @70
    @48
    @51
    @70
    @47
    @45
    @70
    @3
    @46
    @70
    @3
    @46
    wne
    #
    @66
    @65
    @66
    @64
    @68
    @61
    simpr2r
    @61
    @75
    @66
    wb
    @69
    @61
    @3
    cB
    @46
    cD
    @72
    @60
    @59
    @57
    @58
    @59
    simpr
    adantl
    neeq12d
    adantr
    mpbird
    necomd
    a1d
    @70
    @50
    @49
    @70
    @50
    cD
    cC
    wne
    #
    @69
    @76
    @61
    @69
    cC
    cD
    @64
    @67
    @68
    simp3
    necomd
    adantl
    @61
    @50
    @76
    wb
    #
    @69
    @60
    @77
    @57
    @59
    @58
    @77
    @59
    @58
    wa
    @46
    cD
    @7
    cC
    @59
    @58
    simpl
    @59
    @58
    simpr
    neeq12d
    ancoms
    adantl
    adantr
    mpbird
    a1d
    jca
    jca31
    jca31
    syl2anc
    @13
    @10
    vk
    cc0
    c1
    cpr
    #
    c2
    c3
    cpr
    #
    cun
    #
    wral
    @10
    vk
    @78
    wral
    #
    @10
    vk
    @79
    wral
    #
    wa
    @54
    @10
    vk
    @12
    @80
    @12
    cc0
    c4
    cfzo
    co
    @80
    @11
    c4
    cc0
    cfzo
    @11
    cA
    cB
    cC
    cD
    cs4
    #
    chash
    cfv
    c4
    cP
    @83
    chash
    3wlkd.p
    fveq2i
    cA
    cB
    cC
    cD
    s4len
    eqtri
    oveq2i
    fzo0to42pr
    eqtri
    raleqi
    @10
    vk
    @78
    @79
    ralunb
    @81
    @37
    @82
    @53
    @10
    @29
    @36
    vk
    cc0
    c1
    c0ex
    1ex
    @0
    cc0
    wceq
    #
    @5
    @25
    @9
    @28
    @84
    @1
    @22
    @4
    @24
    @0
    cc0
    c1
    neeq1
    @84
    @2
    @23
    @3
    @0
    cc0
    cP
    fveq2
    #
    neeq1d
    imbi12d
    @84
    @6
    @26
    @8
    @27
    @0
    cc0
    c2
    neeq1
    @84
    @2
    @23
    @7
    @85
    neeq1d
    imbi12d
    anbi12d
    @0
    c1
    wceq
    #
    @5
    @32
    @9
    @35
    @86
    @1
    @30
    @4
    @31
    @0
    c1
    c1
    neeq1
    @86
    @2
    @3
    @3
    @0
    c1
    cP
    fveq2
    #
    neeq1d
    imbi12d
    @86
    @6
    @33
    @8
    @34
    @0
    c1
    c2
    neeq1
    @86
    @2
    @3
    @7
    @87
    neeq1d
    imbi12d
    anbi12d
    ralpr
    @10
    @44
    @52
    vk
    c2
    c3
    2ex
    3ex
    @0
    c2
    wceq
    #
    @5
    @40
    @9
    @43
    @88
    @1
    @38
    @4
    @39
    @0
    c2
    c1
    neeq1
    @88
    @2
    @7
    @3
    @0
    c2
    cP
    fveq2
    #
    neeq1d
    imbi12d
    @88
    @6
    @41
    @8
    @42
    @0
    c2
    c2
    neeq1
    @88
    @2
    @7
    @7
    @89
    neeq1d
    imbi12d
    anbi12d
    @0
    c3
    wceq
    #
    @5
    @48
    @9
    @51
    @90
    @1
    @45
    @4
    @47
    @0
    c3
    c1
    neeq1
    @90
    @2
    @46
    @3
    @0
    c3
    cP
    fveq2
    #
    neeq1d
    imbi12d
    @90
    @6
    @49
    @8
    @50
    @0
    c3
    c2
    neeq1
    @90
    @2
    @46
    @7
    @91
    neeq1d
    imbi12d
    anbi12d
    ralpr
    anbi12i
    3bitri
    sylibr
    @21
    @10
    vk
    @12
    @21
    @18
    vj
    c1
    c2
    cpr
    #
    wral
    @10
    @18
    vj
    @20
    @92
    @20
    c1
    c3
    cfzo
    co
    @92
    @19
    c3
    c1
    cfzo
    @19
    cJ
    cK
    cL
    cs3
    #
    chash
    cfv
    c3
    cF
    @93
    chash
    3wlkd.f
    fveq2i
    cJ
    cK
    cL
    s3len
    eqtri
    oveq2i
    fzo13pr
    eqtri
    raleqi
    @18
    @5
    @9
    vj
    c1
    c2
    1ex
    2ex
    @14
    c1
    wceq
    #
    @15
    @1
    @17
    @4
    @14
    c1
    @0
    neeq2
    @94
    @16
    @3
    @2
    @14
    c1
    cP
    fveq2
    neeq2d
    imbi12d
    @14
    c2
    wceq
    #
    @15
    @6
    @17
    @8
    @14
    c2
    @0
    neeq2
    @95
    @16
    @7
    @2
    @14
    c2
    cP
    fveq2
    neeq2d
    imbi12d
    ralpr
    bitri
    ralbii
    sylibr
end
