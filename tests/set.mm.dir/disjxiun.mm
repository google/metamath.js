include "wdisj.mm"
include "ciun.mm"
include "wral.mm"
include "wa.mm"
include "wi.mm"
include "nfiu1.mm"
include "nfcv.mm"
include "nfdisj.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "disjss1.mm"
include "ssiun2.mm"
include "syl11.mm"
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
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbviun.mm"
include "syl6sseqr.mm"
include "adantr.mm"
include "ad2antrl.mm"
include "csbeq1.mm"
include "sseq1d.mm"
include "vtoclga.mm"
include "adantl.mm"
include "cbvdisj.mm"
include "disjor.mm"
include "sylbb.mm"
include "rsp2.mm"
include "syl.mm"
include "imp.mm"
include "ord.mm"
include "impr.mm"
include "adantlr.mm"
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
include "disjeq1d.mm"
include "rspc.mm"
include "impcom.mm"
include "disjors.mm"
include "sylib.mm"
include "ad2ant2r.mm"
include "simplrl.mm"
include "eleqtrrd.mm"
include "jca.mm"
include "syl2an2r.mm"
include "adantlrr.mm"
include "mpd.mm"
include "wne.mm"
include "ss2in.mm"
include "syl2an.mm"
include "biimpi.mm"
include "ad3antlr.mm"
include "id.mm"
include "disji2.mm"
include "syl2an3an.mm"
include "sseq0.mm"
include "pm2.61dane.mm"
include "rexlimdvva.mm"
include "syl5bi.mm"
include "ralrimivv.mm"
include "impbid1.mm"

theorem disjxiun
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
    cB
    @1
    wss
    @2
    @3
    vy
    cv
    cA
    wcel
    vx
    cB
    @1
    cC
    disjss1
    vy
    cA
    cB
    ssiun2
    syl11
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
    @9
    vu
    vv
    weq
    #
    @12
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
    @13
    @9
    @20
    vu
    vv
    cA
    cA
    @9
    @10
    cA
    wcel
    #
    @15
    cA
    wcel
    #
    wa
    #
    wa
    @14
    @19
    @9
    @23
    @14
    wn
    #
    @19
    @9
    @23
    @24
    wa
    #
    wa
    @2
    @11
    @1
    wss
    #
    @16
    @1
    wss
    #
    @11
    @16
    cin
    c0
    wceq
    #
    @19
    @0
    @2
    @25
    simplr
    @23
    @26
    @9
    @24
    @21
    @26
    @22
    @21
    @11
    vu
    cA
    @11
    ciun
    #
    @1
    vu
    cA
    @11
    ssiun2
    vy
    vu
    cA
    cB
    @11
    vu
    cB
    nfcv
    #
    vy
    @10
    cB
    nfcsb1v
    #
    vy
    @10
    cB
    csbeq1a
    #
    cbviun
    #
    syl6sseqr
    #
    adantr
    ad2antrl
    @23
    @27
    @9
    @24
    @22
    @27
    @21
    @26
    @27
    vu
    @15
    cA
    @14
    @11
    @16
    @1
    vy
    @10
    @15
    cB
    csbeq1
    #
    sseq1d
    @34
    vtoclga
    adantl
    ad2antrl
    @0
    @25
    @28
    @2
    @0
    @23
    @24
    @28
    @0
    @23
    wa
    @14
    @28
    @0
    @23
    @14
    @28
    wo
    #
    @0
    @36
    vv
    cA
    wral
    vu
    cA
    wral
    #
    @23
    @36
    wi
    @0
    vu
    cA
    @11
    wdisj
    @37
    vy
    vu
    cA
    cB
    @11
    @30
    @31
    @32
    cbvdisj
    cA
    @11
    @16
    vu
    vv
    @35
    disjor
    sylbb
    @36
    vu
    vv
    cA
    cA
    rsp2
    syl
    imp
    ord
    impr
    adantlr
    vx
    @1
    cC
    @11
    @16
    disjiun
    syl13anc
    expr
    orrd
    ralrimivva
    cA
    @12
    @17
    vu
    vv
    @14
    vx
    @11
    @16
    cC
    @35
    iuneq1d
    disjor
    sylibr
    vy
    vu
    cA
    @5
    @12
    vu
    @5
    nfcv
    vx
    vy
    @11
    cC
    @31
    @8
    nfiun
    vy
    vu
    weq
    #
    vx
    cB
    @11
    cC
    @32
    iuneq1d
    cbvdisj
    sylibr
    ex
    jcad
    @7
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
    @7
    @46
    vr
    vs
    @1
    @1
    @40
    @1
    wcel
    #
    @42
    @1
    wcel
    #
    wa
    #
    @40
    @11
    wcel
    #
    @42
    @16
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
    @7
    @46
    @49
    @50
    vu
    cA
    wrex
    #
    @51
    vv
    cA
    wrex
    #
    wa
    @53
    @47
    @54
    @48
    @55
    @47
    @40
    @29
    wcel
    @54
    @1
    @29
    @40
    @33
    eleq2i
    vu
    @40
    cA
    @11
    eliun
    bitri
    @48
    @42
    vv
    cA
    @16
    ciun
    #
    wcel
    @55
    @1
    @56
    @42
    vy
    vv
    cA
    cB
    @16
    vv
    cB
    nfcv
    vy
    @15
    cB
    nfcsb1v
    vy
    @15
    cB
    csbeq1a
    cbviun
    eleq2i
    vv
    @42
    cA
    @16
    eliun
    bitri
    anbi12i
    @50
    @51
    vu
    vv
    cA
    cA
    reeanv
    bitr4i
    @7
    @52
    @46
    vu
    vv
    cA
    cA
    @7
    @23
    wa
    #
    @52
    @46
    @57
    @52
    wa
    #
    @39
    @45
    @57
    @52
    @39
    wn
    #
    @45
    @57
    @52
    @59
    wa
    #
    wa
    #
    @45
    @10
    @15
    @61
    @14
    wa
    #
    @59
    @45
    @57
    @52
    @59
    @14
    simplrr
    @62
    @39
    @45
    @57
    @52
    @14
    @46
    @59
    @58
    @46
    vs
    @11
    wral
    vr
    @11
    wral
    #
    @14
    @50
    @42
    @11
    wcel
    #
    wa
    #
    @46
    @57
    @63
    @52
    @4
    @21
    @63
    @6
    @22
    @4
    @21
    wa
    vx
    @11
    cC
    wdisj
    #
    @63
    @21
    @4
    @66
    @3
    @66
    vy
    @10
    cA
    vx
    vy
    @11
    cC
    @31
    @8
    nfdisj
    @38
    vx
    cB
    @11
    cC
    @32
    disjeq1d
    rspc
    impcom
    vx
    @11
    cC
    vr
    vs
    disjors
    sylib
    ad2ant2r
    adantr
    @58
    @14
    wa
    #
    @50
    @64
    @57
    @50
    @51
    @14
    simplrl
    @67
    @42
    @16
    @11
    @57
    @50
    @51
    @14
    simplrr
    @14
    @11
    @16
    wceq
    @58
    @35
    adantl
    eleqtrrd
    jca
    @63
    @65
    @46
    @46
    vr
    vs
    @11
    @11
    rsp2
    imp
    syl2an2r
    adantlrr
    ord
    mpd
    @61
    @44
    @18
    wss
    #
    @10
    @15
    wne
    #
    @19
    @45
    @52
    @68
    @57
    @59
    @50
    @41
    @12
    wss
    @43
    @17
    wss
    @68
    @51
    @50
    @41
    vr
    @11
    @41
    ciun
    @12
    vr
    @11
    @41
    ssiun2
    vx
    vr
    @11
    cC
    @41
    vr
    cC
    nfcv
    vx
    @40
    cC
    nfcsb1v
    vx
    @40
    cC
    csbeq1a
    cbviun
    syl6sseqr
    @51
    @43
    vs
    @16
    @43
    ciun
    @17
    vs
    @16
    @43
    ssiun2
    vx
    vs
    @16
    cC
    @43
    vs
    cC
    nfcv
    vx
    @42
    cC
    nfcsb1v
    vx
    @42
    cC
    csbeq1a
    cbviun
    syl6sseqr
    @41
    @12
    @43
    @17
    ss2in
    syl2an
    ad2antrl
    @61
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
    @23
    @69
    @69
    @19
    @6
    @73
    @4
    @23
    @60
    @6
    @73
    vy
    vz
    cA
    @5
    @72
    vz
    @5
    nfcv
    vx
    vy
    @71
    cC
    vy
    @70
    cB
    nfcsb1v
    @8
    nfiun
    vy
    vz
    weq
    vx
    cB
    @71
    cC
    vy
    @70
    cB
    csbeq1a
    iuneq1d
    cbvdisj
    biimpi
    ad3antlr
    @7
    @23
    @60
    simplr
    @69
    id
    vz
    cA
    @72
    @12
    @17
    @10
    @15
    vz
    vu
    weq
    vx
    @71
    @11
    cC
    vy
    @70
    @10
    cB
    csbeq1
    iuneq1d
    vz
    vv
    weq
    vx
    @71
    @16
    cC
    vy
    @70
    @15
    cB
    csbeq1
    iuneq1d
    disji2
    syl2an3an
    @44
    @18
    sseq0
    syl2an2r
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
    impbid1
end
