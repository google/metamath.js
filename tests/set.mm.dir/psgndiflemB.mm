include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "cword.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cgsu.mm"
include "co.mm"
include "chash.mm"
include "wral.mm"
include "cc0.mm"
include "cfzo.mm"
include "w3a.mm"
include "wfn.mm"
include "wf.mm"
include "elrabi.mm"
include "csymg.mm"
include "eqid.mm"
include "symgbasf.mm"
include "ffn.mm"
include "3syl.mm"
include "ad3antlr.mm"
include "simpl.mm"
include "adantr.mm"
include "simp1.mm"
include "anim12i.mm"
include "cbs.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "gsmtrcl.mm"
include "syl.mm"
include "wi.mm"
include "ad3antrrr.mm"
include "simpr.mm"
include "wss.mm"
include "symgtrf.mm"
include "sswrd.mm"
include "sseld.mm"
include "ax-mp.mm"
include "3ad2ant1.mm"
include "adantl.mm"
include "3jca.mm"
include "ralimi.mm"
include "3ad2ant3.mm"
include "wb.mm"
include "oveq2.mm"
include "eqcoms.mm"
include "raleqdv.mm"
include "3ad2ant2.mm"
include "mpbird.mm"
include "gsmsymgrfix.mm"
include "sylc.mm"
include "eqcomd.mm"
include "fveq2.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "simprbi.mm"
include "sylan9eqr.mm"
include "eqeq12d.mm"
include "ex.mm"
include "com12.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "biimpri.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "fvres.mm"
include "exp31.mm"
include "imp.mm"
include "impcom.mm"
include "anim2i.mm"
include "diffi.mm"
include "ancri.mm"
include "ad2antrl.mm"
include "simpr2.mm"
include "jca.mm"
include "cin.mm"
include "incom.mm"
include "indif.mm"
include "gsmsymgreq.mm"
include "weq.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"
include "pm2.61i.mm"
include "eqfnfvd.mm"

theorem psgndiflemB
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let vi: setvar i
  let vn: setvar n
  let cK: class K
  let cN: class N
  let cW: class W
  let cZ: class Z
  let vq: setvar q
  let vw: setvar w
  let vk: setvar k
  assume psgnfix.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume psgnfix.t: |- T = ran ( pmTrsp ` ( N \ { K } ) )
  assume psgnfix.s: |- S = ( SymGrp ` ( N \ { K } ) )
  assume psgnfix.z: |- Z = ( SymGrp ` N )
  assume psgnfix.r: |- R = ran ( pmTrsp ` N )

  disjoint K q
  disjoint P q
  disjoint Q q
  disjoint K i
  disjoint K n
  disjoint i n
  disjoint N i
  disjoint N n
  disjoint S i
  disjoint S n
  disjoint U i
  disjoint U n
  disjoint W i
  disjoint W n
  disjoint Z i
  disjoint Z n
  disjoint K w
  disjoint N w
  disjoint Q w
  disjoint S w
  disjoint T w
  disjoint R w
  disjoint Z w
  disjoint k q
  disjoint K k
  disjoint i k
  disjoint k n
  disjoint N k
  disjoint P k
  disjoint Q k
  disjoint R k
  disjoint S k
  disjoint T k
  disjoint U k
  disjoint W k
  disjoint Z k
  assert |- ( ( ( N e. Fin /\ K e. N ) /\ Q e. { q e. P | ( q ` K ) = K } ) -> ( ( W e. Word T /\ ( Q |` ( N \ { K } ) ) = ( S gsum W ) ) -> ( ( U e. Word R /\ ( # ` W ) = ( # ` U ) /\ A. i e. ( 0 ..^ ( # ` W ) ) ( ( ( U ` i ) ` K ) = K /\ A. n e. ( N \ { K } ) ( ( W ` i ) ` n ) = ( ( U ` i ) ` n ) ) ) -> Q = ( Z gsum U ) ) ) )

  proof
    cN
    cfn
    wcel
    #
    cK
    cN
    wcel
    #
    wa
    #
    cQ
    cK
    vq
    cv
    #
    cfv
    #
    cK
    wceq
    #
    vq
    cP
    crab
    wcel
    #
    wa
    #
    cW
    cT
    cword
    #
    wcel
    #
    cQ
    cN
    cK
    csn
    #
    cdif
    #
    cres
    #
    cS
    cW
    cgsu
    co
    #
    wceq
    #
    wa
    #
    cU
    cR
    cword
    #
    wcel
    #
    cW
    chash
    cfv
    #
    cU
    chash
    cfv
    #
    wceq
    #
    cK
    vi
    cv
    #
    cU
    cfv
    #
    cfv
    cK
    wceq
    #
    vn
    cv
    #
    @21
    cW
    cfv
    cfv
    @24
    @22
    cfv
    wceq
    vn
    @11
    wral
    #
    wa
    #
    vi
    cc0
    @18
    cfzo
    co
    #
    wral
    #
    w3a
    #
    cQ
    cZ
    cU
    cgsu
    co
    #
    wceq
    @7
    @15
    wa
    #
    @29
    wa
    #
    vk
    cN
    cQ
    @30
    @6
    cQ
    cN
    wfn
    #
    @2
    @15
    @29
    @6
    cQ
    cP
    wcel
    #
    cN
    cN
    cQ
    wf
    @33
    @5
    vq
    cQ
    cP
    elrabi
    cN
    cP
    cQ
    cN
    csymg
    cfv
    #
    @35
    eqid
    #
    psgnfix.p
    symgbasf
    cN
    cN
    cQ
    ffn
    3syl
    ad3antlr
    @32
    @30
    cP
    wcel
    #
    cN
    cN
    @30
    wf
    @30
    cN
    wfn
    @32
    @0
    @17
    wa
    @37
    @31
    @0
    @29
    @17
    @7
    @0
    @15
    @2
    @0
    @6
    @0
    @1
    simpl
    #
    adantr
    adantr
    @17
    @20
    @28
    simp1
    anim12i
    cP
    cZ
    cR
    cN
    cU
    psgnfix.z
    cP
    @35
    cbs
    cfv
    cZ
    cbs
    cfv
    #
    psgnfix.p
    @35
    cZ
    cbs
    cZ
    @35
    psgnfix.z
    eqcomi
    fveq2i
    eqtri
    psgnfix.r
    gsmtrcl
    syl
    cN
    cP
    @30
    @35
    @36
    psgnfix.p
    symgbasf
    cN
    cN
    @30
    ffn
    3syl
    vk
    cv
    #
    cK
    wceq
    #
    @32
    @40
    cN
    wcel
    #
    wa
    #
    @40
    cQ
    cfv
    #
    @40
    @30
    cfv
    #
    wceq
    #
    wi
    @43
    @41
    @46
    @32
    @41
    @46
    wi
    @42
    @32
    @41
    @46
    @32
    @41
    wa
    #
    @46
    cK
    cK
    @30
    cfv
    #
    wceq
    #
    @32
    @49
    @41
    @32
    @48
    cK
    @32
    @0
    @1
    cU
    @39
    cword
    #
    wcel
    #
    w3a
    @23
    vi
    cc0
    @19
    cfzo
    co
    #
    wral
    #
    @48
    cK
    wceq
    @32
    @0
    @1
    @51
    @2
    @0
    @6
    @15
    @29
    @38
    ad3antrrr
    @2
    @1
    @6
    @15
    @29
    @0
    @1
    simpr
    ad3antrrr
    @29
    @51
    @31
    @17
    @20
    @51
    @28
    cR
    @39
    wss
    #
    @17
    @51
    wi
    @39
    cN
    cR
    cZ
    psgnfix.r
    psgnfix.z
    @39
    eqid
    #
    symgtrf
    @54
    @16
    @50
    cU
    cR
    @39
    sswrd
    sseld
    ax-mp
    3ad2ant1
    adantl
    #
    3jca
    @32
    @53
    @23
    vi
    @27
    wral
    #
    @29
    @57
    @31
    @28
    @17
    @57
    @20
    @26
    @23
    vi
    @27
    @23
    @25
    simpl
    ralimi
    3ad2ant3
    adantl
    @29
    @53
    @57
    wb
    #
    @31
    @20
    @17
    @58
    @28
    @20
    @23
    vi
    @52
    @27
    @52
    @27
    wceq
    @19
    @18
    @19
    @18
    cc0
    cfzo
    oveq2
    eqcoms
    raleqdv
    3ad2ant2
    adantl
    mpbird
    @39
    cZ
    vi
    cK
    cN
    cU
    psgnfix.z
    @55
    gsmsymgrfix
    sylc
    eqcomd
    adantr
    @47
    @44
    cK
    @45
    @48
    @41
    @32
    @44
    cK
    cQ
    cfv
    #
    cK
    @40
    cK
    cQ
    fveq2
    @6
    @59
    cK
    wceq
    #
    @2
    @15
    @29
    @6
    @34
    @60
    @5
    @60
    vq
    cQ
    cP
    @3
    cQ
    wceq
    @4
    @59
    cK
    cK
    @3
    cQ
    fveq1
    eqeq1d
    elrab
    simprbi
    ad3antlr
    sylan9eqr
    @41
    @45
    @48
    wceq
    @32
    @40
    cK
    @30
    fveq2
    adantl
    eqeq12d
    mpbird
    ex
    adantr
    com12
    @41
    wn
    #
    @43
    @46
    @61
    @43
    wa
    #
    @40
    @12
    cfv
    #
    @40
    @13
    cfv
    #
    @44
    @45
    @43
    @63
    @64
    wceq
    #
    @61
    @15
    @65
    @7
    @29
    @42
    @14
    @65
    @9
    @40
    @12
    @13
    fveq1
    adantl
    ad3antlr
    adantl
    @43
    @61
    @63
    @44
    wceq
    #
    @32
    @42
    @61
    @66
    wi
    #
    @2
    @42
    @67
    wi
    @6
    @15
    @29
    @2
    @42
    @61
    @66
    @2
    @42
    wa
    #
    @61
    wa
    #
    @40
    @11
    wcel
    #
    @66
    @69
    @42
    @40
    cK
    wne
    #
    wa
    #
    @70
    @68
    @42
    @61
    @71
    @2
    @42
    simpr
    @71
    @61
    @40
    cK
    df-ne
    biimpri
    #
    anim12i
    @40
    cN
    cK
    eldifsn
    #
    sylibr
    @40
    @11
    cQ
    fvres
    syl
    exp31
    ad3antrrr
    imp
    impcom
    @62
    @70
    @24
    @13
    cfv
    #
    @24
    @30
    cfv
    #
    wceq
    #
    vn
    @11
    wral
    #
    @64
    @45
    wceq
    #
    @43
    @61
    @70
    @42
    @61
    @70
    wi
    @32
    @42
    @61
    @70
    @42
    @61
    wa
    @72
    @70
    @61
    @71
    @42
    @73
    anim2i
    @74
    sylibr
    ex
    adantl
    impcom
    @62
    @11
    cfn
    wcel
    #
    @0
    wa
    #
    cW
    cS
    cbs
    cfv
    #
    cword
    #
    wcel
    #
    @51
    @20
    w3a
    #
    wa
    #
    @25
    vi
    @27
    wral
    #
    @78
    @32
    @86
    @61
    @42
    @32
    @81
    @85
    @2
    @81
    @6
    @15
    @29
    @0
    @81
    @1
    @0
    @80
    cN
    @10
    diffi
    ancri
    adantr
    ad3antrrr
    @32
    @84
    @51
    @20
    @31
    @84
    @29
    @9
    @84
    @7
    @14
    cT
    @82
    wss
    #
    @9
    @84
    wi
    @82
    @11
    cT
    cS
    psgnfix.t
    psgnfix.s
    @82
    eqid
    #
    symgtrf
    @88
    @8
    @83
    cW
    cT
    @82
    sswrd
    sseld
    ax-mp
    ad2antrl
    adantr
    @56
    @31
    @17
    @20
    @28
    simpr2
    3jca
    jca
    ad2antrl
    @32
    @87
    @61
    @42
    @29
    @87
    @31
    @28
    @17
    @87
    @20
    @26
    @25
    vi
    @27
    @23
    @25
    simpr
    ralimi
    3ad2ant3
    adantl
    ad2antrl
    @82
    @39
    cS
    cU
    vi
    vn
    @11
    cN
    @11
    cW
    cZ
    psgnfix.s
    @89
    psgnfix.z
    @55
    @11
    cN
    cin
    #
    @11
    @90
    cN
    @11
    cin
    @11
    @11
    cN
    incom
    cN
    @10
    indif
    eqtri
    eqcomi
    gsmsymgreq
    sylc
    @77
    @79
    vn
    @40
    @11
    vn
    vk
    weq
    @75
    @64
    @76
    @45
    @24
    @40
    @13
    fveq2
    @24
    @40
    @30
    fveq2
    eqeq12d
    rspcva
    syl2anc
    3eqtr3d
    ex
    pm2.61i
    eqfnfvd
    exp31
end
