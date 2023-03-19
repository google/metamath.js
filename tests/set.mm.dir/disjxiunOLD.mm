include "wdisj.mm"
include "ciun.mm"
include "wral.mm"
include "wa.mm"
include "wi.mm"
include "nfiu1.mm"
include "nfcv.mm"
include "nfdisj.mm"
include "cv.mm"
include "wcel.mm"
include "wss.mm"
include "ssiun2.mm"
include "disjss1.mm"
include "syl.mm"
include "com12.mm"
include "ralrimi.mm"
include "a1i.mm"
include "csb.mm"
include "weq.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "simplr.mm"
include "simprll.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbviun.mm"
include "syl6sseqr.mm"
include "simprlr.mm"
include "csbeq1.mm"
include "sseq1d.mm"
include "vtoclga.mm"
include "simpl.mm"
include "cbvdisj.mm"
include "sylib.mm"
include "disjor.mm"
include "rsp2.mm"
include "imp.mm"
include "ord.mm"
include "impr.mm"
include "disjiun.mm"
include "syl13anc.mm"
include "expr.mm"
include "orrd.mm"
include "ralrimivva.mm"
include "iuneq1d.mm"
include "sylibr.mm"
include "nfiun.mm"
include "ex.mm"
include "jcad.mm"
include "wrex.mm"
include "eleq2i.mm"
include "eliun.mm"
include "bitri.mm"
include "anbi12i.mm"
include "reeanv.mm"
include "bitr4i.mm"
include "simplrr.mm"
include "simprl.mm"
include "simplrl.mm"
include "disjeq1d.mm"
include "rspc.mm"
include "sylc.mm"
include "ad2antrr.mm"
include "disjors.mm"
include "simpld.mm"
include "simprd.mm"
include "adantl.mm"
include "eleqtrrd.mm"
include "jca.mm"
include "mpd.mm"
include "wne.mm"
include "ss2in.mm"
include "syl2anc.mm"
include "simprr.mm"
include "simpr.mm"
include "disji2.mm"
include "syl121anc.mm"
include "sseq0.mm"
include "pm2.61dane.mm"
include "rexlimdvva.mm"
include "syl5bi.mm"
include "ralrimivv.mm"
include "impbid.mm"

theorem disjxiunOLD
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vr: setvar r
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint C y
  disjoint r s
  disjoint r u
  disjoint r v
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B r
  disjoint B s
  disjoint B u
  disjoint B v
  disjoint B z
  disjoint C r
  disjoint C s
  disjoint C u
  disjoint C v
  disjoint C z
  assert |- ( Disj_ y e. A B -> ( Disj_ x e. U_ y e. A B C <-> ( A. y e. A Disj_ x e. B C /\ Disj_ y e. A U_ x e. B C ) ) )

  proof
    vy
    cA
    cB
    wdisj
    #
    vx
    vy
    cA
    cB
    ciun
    #
    cC
    wdisj
    #
    vx
    cB
    cC
    wdisj
    #
    vy
    cA
    wral
    #
    vy
    cA
    vx
    cB
    cC
    ciun
    #
    wdisj
    #
    wa
    #
    @0
    @2
    @4
    @6
    @2
    @4
    wi
    @0
    @2
    @3
    vy
    cA
    vx
    vy
    @1
    cC
    vy
    cA
    cB
    nfiu1
    vy
    cC
    nfcv
    #
    nfdisj
    vy
    cv
    cA
    wcel
    #
    @2
    @3
    @9
    cB
    @1
    wss
    @2
    @3
    wi
    vy
    cA
    cB
    ssiun2
    vx
    cB
    @1
    cC
    disjss1
    syl
    com12
    ralrimi
    a1i
    @0
    @2
    @6
    @0
    @2
    wa
    #
    vu
    cA
    vx
    vy
    vu
    cv
    #
    cB
    csb
    #
    cC
    ciun
    #
    wdisj
    #
    @6
    @10
    vu
    vv
    weq
    #
    @13
    vx
    vy
    vv
    cv
    #
    cB
    csb
    #
    cC
    ciun
    #
    cin
    #
    c0
    wceq
    #
    wo
    #
    vv
    cA
    wral
    vu
    cA
    wral
    @14
    @10
    @21
    vu
    vv
    cA
    cA
    @10
    @11
    cA
    wcel
    #
    @16
    cA
    wcel
    #
    wa
    #
    wa
    #
    @15
    @20
    @10
    @24
    @15
    wn
    #
    @20
    @10
    @24
    @26
    wa
    #
    wa
    #
    @2
    @12
    @1
    wss
    #
    @17
    @1
    wss
    #
    @12
    @17
    cin
    c0
    wceq
    #
    @20
    @0
    @2
    @27
    simplr
    @28
    @22
    @29
    @10
    @22
    @23
    @26
    simprll
    @22
    @12
    vu
    cA
    @12
    ciun
    #
    @1
    vu
    cA
    @12
    ssiun2
    vy
    vu
    cA
    cB
    @12
    vu
    cB
    nfcv
    #
    vy
    @11
    cB
    nfcsb1v
    #
    vy
    @11
    cB
    csbeq1a
    #
    cbviun
    #
    syl6sseqr
    #
    syl
    @28
    @23
    @30
    @10
    @22
    @23
    @26
    simprlr
    @29
    @30
    vu
    @16
    cA
    @15
    @12
    @17
    @1
    vy
    @11
    @16
    cB
    csbeq1
    #
    sseq1d
    @37
    vtoclga
    syl
    @10
    @24
    @26
    @31
    @25
    @15
    @31
    @10
    @24
    @15
    @31
    wo
    #
    @10
    @39
    vv
    cA
    wral
    vu
    cA
    wral
    #
    @24
    @39
    wi
    @10
    vu
    cA
    @12
    wdisj
    #
    @40
    @10
    @0
    @41
    @0
    @2
    simpl
    vy
    vu
    cA
    cB
    @12
    @33
    @34
    @35
    cbvdisj
    sylib
    cA
    @12
    @17
    vu
    vv
    @38
    disjor
    sylib
    @39
    vu
    vv
    cA
    cA
    rsp2
    syl
    imp
    ord
    impr
    vx
    @1
    cC
    @12
    @17
    disjiun
    syl13anc
    expr
    orrd
    ralrimivva
    cA
    @13
    @18
    vu
    vv
    @15
    vx
    @12
    @17
    cC
    @38
    iuneq1d
    disjor
    sylibr
    vy
    vu
    cA
    @5
    @13
    vu
    @5
    nfcv
    vx
    vy
    @12
    cC
    @34
    @8
    nfiun
    vy
    vu
    weq
    #
    vx
    cB
    @12
    cC
    @35
    iuneq1d
    cbvdisj
    sylibr
    ex
    jcad
    @0
    @7
    @2
    @0
    @7
    wa
    #
    vr
    vs
    weq
    #
    vx
    vr
    cv
    #
    cC
    csb
    #
    vx
    vs
    cv
    #
    cC
    csb
    #
    cin
    #
    c0
    wceq
    #
    wo
    #
    vs
    @1
    wral
    vr
    @1
    wral
    @2
    @43
    @51
    vr
    vs
    @1
    @1
    @45
    @1
    wcel
    #
    @47
    @1
    wcel
    #
    wa
    #
    @45
    @12
    wcel
    #
    @47
    @17
    wcel
    #
    wa
    #
    vv
    cA
    wrex
    vu
    cA
    wrex
    #
    @43
    @51
    @54
    @55
    vu
    cA
    wrex
    #
    @56
    vv
    cA
    wrex
    #
    wa
    @58
    @52
    @59
    @53
    @60
    @52
    @45
    @32
    wcel
    @59
    @1
    @32
    @45
    @36
    eleq2i
    vu
    @45
    cA
    @12
    eliun
    bitri
    @53
    @47
    vv
    cA
    @17
    ciun
    #
    wcel
    @60
    @1
    @61
    @47
    vy
    vv
    cA
    cB
    @17
    vv
    cB
    nfcv
    vy
    @16
    cB
    nfcsb1v
    vy
    @16
    cB
    csbeq1a
    cbviun
    eleq2i
    vv
    @47
    cA
    @17
    eliun
    bitri
    anbi12i
    @55
    @56
    vu
    vv
    cA
    cA
    reeanv
    bitr4i
    @43
    @57
    @51
    vu
    vv
    cA
    cA
    @43
    @24
    wa
    #
    @57
    @51
    @62
    @57
    wa
    @44
    @50
    @62
    @57
    @44
    wn
    #
    @50
    @62
    @57
    @63
    wa
    #
    wa
    #
    @50
    @11
    @16
    @65
    @15
    wa
    #
    @63
    @50
    @62
    @57
    @63
    @15
    simplrr
    @66
    @44
    @50
    @66
    @51
    vs
    @12
    wral
    vr
    @12
    wral
    #
    @55
    @47
    @12
    wcel
    #
    wa
    @51
    @66
    vx
    @12
    cC
    wdisj
    #
    @67
    @62
    @69
    @64
    @15
    @62
    @22
    @4
    @69
    @43
    @22
    @23
    simprl
    #
    @0
    @4
    @6
    @24
    simplrl
    @3
    @69
    vy
    @11
    cA
    vx
    vy
    @12
    cC
    @34
    @8
    nfdisj
    @42
    vx
    cB
    @12
    cC
    @35
    disjeq1d
    rspc
    sylc
    ad2antrr
    vx
    @12
    cC
    vr
    vs
    disjors
    sylib
    @66
    @55
    @68
    @66
    @55
    @56
    @62
    @57
    @63
    @15
    simplrl
    #
    simpld
    @66
    @47
    @17
    @12
    @66
    @55
    @56
    @71
    simprd
    @15
    @12
    @17
    wceq
    @65
    @38
    adantl
    eleqtrrd
    jca
    @51
    vr
    vs
    @12
    @12
    rsp2
    sylc
    ord
    mpd
    @65
    @11
    @16
    wne
    #
    wa
    #
    @49
    @19
    wss
    #
    @20
    @50
    @73
    @46
    @13
    wss
    #
    @48
    @18
    wss
    #
    @74
    @73
    @55
    @75
    @73
    @55
    @56
    @62
    @57
    @63
    @72
    simplrl
    #
    simpld
    @55
    @46
    vr
    @12
    @46
    ciun
    @13
    vr
    @12
    @46
    ssiun2
    vx
    vr
    @12
    cC
    @46
    vr
    cC
    nfcv
    vx
    @45
    cC
    nfcsb1v
    vx
    @45
    cC
    csbeq1a
    cbviun
    syl6sseqr
    syl
    @73
    @56
    @76
    @73
    @55
    @56
    @77
    simprd
    @56
    @48
    vs
    @17
    @48
    ciun
    @18
    vs
    @17
    @48
    ssiun2
    vx
    vs
    @17
    cC
    @48
    vs
    cC
    nfcv
    vx
    @47
    cC
    nfcsb1v
    vx
    @47
    cC
    csbeq1a
    cbviun
    syl6sseqr
    syl
    @46
    @13
    @48
    @18
    ss2in
    syl2anc
    @73
    vz
    cA
    vx
    vy
    vz
    cv
    #
    cB
    csb
    #
    cC
    ciun
    #
    wdisj
    #
    @22
    @23
    @72
    @20
    @73
    @6
    @81
    @62
    @6
    @64
    @72
    @0
    @4
    @6
    @24
    simplrr
    ad2antrr
    vy
    vz
    cA
    @5
    @80
    vz
    @5
    nfcv
    vx
    vy
    @79
    cC
    vy
    @78
    cB
    nfcsb1v
    @8
    nfiun
    vy
    vz
    weq
    vx
    cB
    @79
    cC
    vy
    @78
    cB
    csbeq1a
    iuneq1d
    cbvdisj
    sylib
    @62
    @22
    @64
    @72
    @70
    ad2antrr
    @62
    @23
    @64
    @72
    @43
    @22
    @23
    simprr
    ad2antrr
    @65
    @72
    simpr
    vz
    cA
    @80
    @13
    @18
    @11
    @16
    vz
    vu
    weq
    vx
    @79
    @12
    cC
    vy
    @78
    @11
    cB
    csbeq1
    iuneq1d
    vz
    vv
    weq
    vx
    @79
    @17
    cC
    vy
    @78
    @16
    cB
    csbeq1
    iuneq1d
    disji2
    syl121anc
    @49
    @19
    sseq0
    syl2anc
    pm2.61dane
    expr
    orrd
    ex
    rexlimdvva
    syl5bi
    ralrimivv
    vx
    @1
    cC
    vr
    vs
    disjors
    sylibr
    ex
    impbid
end
