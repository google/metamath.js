include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "ccnp.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "cima.mm"
include "wss.mm"
include "csn.mm"
include "cnei.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "cnpf2.mm"
include "3expa.mm"
include "3adantl3.mm"
include "cnt.mm"
include "simplr.mm"
include "ctop.mm"
include "cuni.mm"
include "simpll2.mm"
include "topontop.mm"
include "syl.mm"
include "eqid.mm"
include "neii1.mm"
include "sylancom.mm"
include "ntropn.mm"
include "syl2anc.mm"
include "simpr.mm"
include "wb.mm"
include "adantr.mm"
include "simpll3.mm"
include "ffvelrnd.mm"
include "wceq.mm"
include "toponuni.mm"
include "eleqtrd.mm"
include "snssd.mm"
include "neiint.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "fvex.mm"
include "snss.mm"
include "sylibr.mm"
include "cnpimaex.mm"
include "simpl1.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "simprrl.mm"
include "opnneip.mm"
include "simprrr.mm"
include "ntrss2.mm"
include "sstrd.mm"
include "jca.mm"
include "ex.mm"
include "reximdv2.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "wi.mm"
include "simprr.mm"
include "snssg.mm"
include "mpbird.mm"
include "imass2.mm"
include "eleq2.mm"
include "imaeq2.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rexlimdvaa.mm"
include "embantd.mm"
include "com23.mm"
include "exp4a.mm"
include "ralimdv2.mm"
include "imdistanda.mm"
include "iscnp.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem iscnp4
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vz: setvar z

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint P x
  disjoint P y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint J z
  disjoint K z
  disjoint P z
  disjoint X z
  disjoint Y z
  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) /\ P e. X ) -> ( F e. ( ( J CnP K ) ` P ) <-> ( F : X --> Y /\ A. y e. ( ( nei ` K ) ` { ( F ` P ) } ) E. x e. ( ( nei ` J ) ` { P } ) ( F " x ) C_ y ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    w3a
    #
    cF
    cP
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    cX
    cY
    cF
    wf
    #
    cF
    vx
    cv
    #
    cima
    #
    vy
    cv
    #
    wss
    #
    vx
    cP
    csn
    #
    cJ
    cnei
    cfv
    cfv
    #
    wrex
    #
    vy
    cP
    cF
    cfv
    #
    csn
    #
    cK
    cnei
    cfv
    cfv
    #
    wral
    #
    wa
    #
    @3
    @4
    @17
    @3
    @4
    wa
    #
    @5
    @16
    @0
    @1
    @4
    @5
    @2
    @0
    @1
    @4
    @5
    cP
    cF
    cJ
    cK
    cX
    cY
    cnpf2
    3expa
    3adantl3
    #
    @18
    @12
    vy
    @15
    @18
    @8
    @15
    wcel
    #
    wa
    #
    cP
    @6
    wcel
    #
    @7
    @8
    cK
    cnt
    cfv
    cfv
    #
    wss
    #
    wa
    #
    vx
    cJ
    wrex
    #
    @12
    @21
    @4
    @23
    cK
    wcel
    #
    @13
    @23
    wcel
    #
    @26
    @3
    @4
    @20
    simplr
    @21
    cK
    ctop
    wcel
    #
    @8
    cK
    cuni
    #
    wss
    #
    @27
    @21
    @1
    @29
    @0
    @1
    @2
    @4
    @20
    simpll2
    #
    cY
    cK
    topontop
    #
    syl
    #
    @18
    @20
    @29
    @31
    @34
    @14
    cK
    @8
    @30
    @30
    eqid
    #
    neii1
    sylancom
    #
    @8
    cK
    @30
    @35
    ntropn
    syl2anc
    @21
    @14
    @23
    wss
    #
    @28
    @21
    @20
    @37
    @18
    @20
    simpr
    @21
    @29
    @14
    @30
    wss
    @31
    @20
    @37
    wb
    @34
    @21
    @13
    @30
    @21
    @13
    cY
    @30
    @21
    cX
    cY
    cP
    cF
    @18
    @5
    @20
    @19
    adantr
    @0
    @1
    @2
    @4
    @20
    simpll3
    ffvelrnd
    @21
    @1
    cY
    @30
    wceq
    @32
    cY
    cK
    toponuni
    syl
    eleqtrd
    snssd
    @36
    @14
    cK
    @8
    @30
    @35
    neiint
    syl3anc
    mpbid
    @13
    @23
    cP
    cF
    fvex
    snss
    sylibr
    vx
    @23
    cP
    cF
    cJ
    cK
    cnpimaex
    syl3anc
    @21
    @25
    @9
    vx
    cJ
    @11
    @21
    @6
    cJ
    wcel
    #
    @25
    wa
    #
    @6
    @11
    wcel
    #
    @9
    wa
    #
    @21
    @39
    wa
    #
    @40
    @9
    @42
    cJ
    ctop
    wcel
    #
    @38
    @22
    @40
    @42
    @0
    @43
    @18
    @0
    @20
    @39
    @0
    @1
    @2
    @4
    simpl1
    ad2antrr
    cX
    cJ
    topontop
    #
    syl
    @21
    @38
    @25
    simprl
    @21
    @38
    @22
    @24
    simprrl
    cP
    cJ
    @6
    opnneip
    syl3anc
    @42
    @7
    @23
    @8
    @21
    @38
    @22
    @24
    simprrr
    @21
    @23
    @8
    wss
    #
    @39
    @21
    @29
    @31
    @45
    @34
    @36
    @8
    cK
    @30
    @35
    ntrss2
    syl2anc
    adantr
    sstrd
    jca
    ex
    reximdv2
    mpd
    ralrimiva
    jca
    ex
    @3
    @17
    @5
    @13
    @8
    wcel
    #
    cP
    vz
    cv
    #
    wcel
    #
    cF
    @47
    cima
    #
    @8
    wss
    #
    wa
    #
    vz
    cJ
    wrex
    #
    wi
    #
    vy
    cK
    wral
    #
    wa
    @4
    @3
    @5
    @16
    @54
    @3
    @5
    wa
    #
    @12
    @53
    vy
    @15
    cK
    @55
    @20
    @12
    wi
    #
    @8
    cK
    wcel
    #
    @46
    @52
    @55
    @57
    @46
    wa
    #
    @56
    @52
    @55
    @58
    @56
    @52
    wi
    @55
    @58
    wa
    #
    @20
    @12
    @52
    @59
    @29
    @57
    @46
    @20
    @59
    @1
    @29
    @0
    @1
    @2
    @5
    @58
    simpll2
    @33
    syl
    @55
    @57
    @46
    simprl
    @55
    @57
    @46
    simprr
    @13
    cK
    @8
    opnneip
    syl3anc
    @59
    @9
    @52
    vx
    @11
    @59
    @41
    wa
    #
    @6
    cJ
    cnt
    cfv
    cfv
    #
    cJ
    wcel
    #
    cP
    @61
    wcel
    #
    cF
    @61
    cima
    #
    @8
    wss
    #
    @52
    @60
    @43
    @6
    cJ
    cuni
    #
    wss
    #
    @62
    @60
    @0
    @43
    @55
    @0
    @58
    @41
    @0
    @1
    @2
    @5
    simpl1
    ad2antrr
    #
    @44
    syl
    #
    @60
    @43
    @40
    @67
    @69
    @59
    @40
    @9
    simprl
    #
    @10
    cJ
    @6
    @66
    @66
    eqid
    #
    neii1
    syl2anc
    #
    @6
    cJ
    @66
    @71
    ntropn
    syl2anc
    @60
    @63
    @10
    @61
    wss
    #
    @60
    @40
    @73
    @70
    @60
    @43
    @10
    @66
    wss
    @67
    @40
    @73
    wb
    @69
    @60
    cP
    @66
    @60
    cP
    cX
    @66
    @59
    @2
    @41
    @0
    @1
    @2
    @5
    @58
    simpll3
    adantr
    #
    @60
    @0
    cX
    @66
    wceq
    @68
    cX
    cJ
    toponuni
    syl
    eleqtrd
    snssd
    @72
    @10
    cJ
    @6
    @66
    @71
    neiint
    syl3anc
    mpbid
    @60
    @2
    @63
    @73
    wb
    @74
    cP
    @61
    cX
    snssg
    syl
    mpbird
    @60
    @64
    @7
    @8
    @60
    @61
    @6
    wss
    #
    @64
    @7
    wss
    @60
    @43
    @67
    @75
    @69
    @72
    @6
    cJ
    @66
    @71
    ntrss2
    syl2anc
    @61
    @6
    cF
    imass2
    syl
    @59
    @40
    @9
    simprr
    sstrd
    @51
    @63
    @65
    wa
    vz
    @61
    cJ
    @47
    @61
    wceq
    #
    @48
    @63
    @50
    @65
    @47
    @61
    cP
    eleq2
    @76
    @49
    @64
    @8
    @47
    @61
    cF
    imaeq2
    sseq1d
    anbi12d
    rspcev
    syl12anc
    rexlimdvaa
    embantd
    ex
    com23
    exp4a
    ralimdv2
    imdistanda
    vz
    vy
    cP
    cF
    cJ
    cK
    cX
    cY
    iscnp
    sylibrd
    impbid
end
