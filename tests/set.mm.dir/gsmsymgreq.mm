include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cfn.mm"
include "wa.mm"
include "cv.mm"
include "wral.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cgsu.mm"
include "wi.mm"
include "c0.mm"
include "cs1.mm"
include "cconcat.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "adantr.mm"
include "fveq1.mm"
include "fveq1d.mm"
include "eqeqan12d.mm"
include "ralbidv.mm"
include "raleqbidv.mm"
include "oveq2.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "eqeq1d.mm"
include "eqeq2d.mm"
include "cid.mm"
include "cres.mm"
include "cin.mm"
include "eleq2.mm"
include "elin.mm"
include "syl6bb.mm"
include "simpl.mm"
include "syl6bi.mm"
include "ax-mp.mm"
include "adantl.mm"
include "fvresi.mm"
include "syl.mm"
include "simpr.mm"
include "eqtr4d.mm"
include "ralrimiva.mm"
include "c0g.mm"
include "symgid.mm"
include "eqid.mm"
include "gsum0.mm"
include "syl6reqr.mm"
include "eqeq12d.mm"
include "mpbird.mm"
include "a1d.mm"
include "gsmsymgreqlem2.mm"
include "expcom.mm"
include "a2d.mm"
include "wrd2ind.mm"
include "impcom.mm"

theorem gsmsymgreq
  let cB: class B
  let cP: class P
  let cS: class S
  let cU: class U
  let vi: setvar i
  let vn: setvar n
  let cI: class I
  let cM: class M
  let cN: class N
  let cW: class W
  let cZ: class Z
  let cK: class K
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cC: class C
  let cJ: class J
  let cR: class R
  let cY: class Y
  let vj: setvar j
  let vp: setvar p
  let vx: setvar x
  let vb: setvar b
  let vu: setvar u
  assume gsmsymgrfix.s: |- S = ( SymGrp ` N )
  assume gsmsymgrfix.b: |- B = ( Base ` S )
  assume gsmsymgreq.z: |- Z = ( SymGrp ` M )
  assume gsmsymgreq.p: |- P = ( Base ` Z )
  assume gsmsymgreq.i: |- I = ( N i^i M )

  disjoint B i
  disjoint N i
  disjoint P i
  disjoint W i
  disjoint I n
  disjoint S n
  disjoint Z n
  disjoint B n
  disjoint i n
  disjoint I i
  disjoint M n
  disjoint N n
  disjoint P n
  disjoint U i
  disjoint U n
  disjoint W n
  disjoint K i
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint i w
  disjoint i y
  disjoint i z
  disjoint w y
  disjoint w z
  disjoint y z
  disjoint K w
  disjoint K y
  disjoint K z
  disjoint N w
  disjoint N y
  disjoint N z
  disjoint S w
  disjoint S y
  disjoint S z
  disjoint W w
  disjoint F n
  disjoint G n
  disjoint H n
  disjoint K n
  disjoint X n
  disjoint C n
  disjoint J n
  disjoint R n
  disjoint Y n
  disjoint C i
  disjoint C j
  disjoint i j
  disjoint j n
  disjoint I j
  disjoint R i
  disjoint R j
  disjoint S j
  disjoint X i
  disjoint X j
  disjoint Y i
  disjoint Y j
  disjoint Z j
  disjoint i p
  disjoint i x
  disjoint p x
  disjoint B b
  disjoint B p
  disjoint B u
  disjoint B x
  disjoint b p
  disjoint b u
  disjoint b x
  disjoint p u
  disjoint u x
  disjoint I b
  disjoint I p
  disjoint I u
  disjoint I w
  disjoint I x
  disjoint I y
  disjoint b w
  disjoint b y
  disjoint p w
  disjoint p y
  disjoint u w
  disjoint u y
  disjoint w x
  disjoint x y
  disjoint M b
  disjoint M p
  disjoint M u
  disjoint M w
  disjoint M x
  disjoint M y
  disjoint b n
  disjoint n p
  disjoint n u
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint N b
  disjoint N p
  disjoint N u
  disjoint N x
  disjoint P b
  disjoint P p
  disjoint P u
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint S b
  disjoint S p
  disjoint S u
  disjoint S x
  disjoint U b
  disjoint U u
  disjoint b i
  disjoint i u
  disjoint U w
  disjoint U x
  disjoint W u
  disjoint Z b
  disjoint Z p
  disjoint Z u
  disjoint Z w
  disjoint Z x
  disjoint Z y
  assert |- ( ( ( N e. Fin /\ M e. Fin ) /\ ( W e. Word B /\ U e. Word P /\ ( # ` W ) = ( # ` U ) ) ) -> ( A. i e. ( 0 ..^ ( # ` W ) ) A. n e. I ( ( W ` i ) ` n ) = ( ( U ` i ) ` n ) -> A. n e. I ( ( S gsum W ) ` n ) = ( ( Z gsum U ) ` n ) ) )

  proof
    cW
    cB
    cword
    #
    wcel
    cU
    cP
    cword
    #
    wcel
    cW
    chash
    cfv
    #
    cU
    chash
    cfv
    wceq
    w3a
    cN
    cfn
    wcel
    #
    cM
    cfn
    wcel
    #
    wa
    #
    vn
    cv
    #
    vi
    cv
    #
    cW
    cfv
    #
    cfv
    #
    @6
    @7
    cU
    cfv
    #
    cfv
    #
    wceq
    #
    vn
    cI
    wral
    #
    vi
    cc0
    @2
    cfzo
    co
    #
    wral
    #
    @6
    cS
    cW
    cgsu
    co
    #
    cfv
    #
    @6
    cZ
    cU
    cgsu
    co
    #
    cfv
    #
    wceq
    #
    vn
    cI
    wral
    #
    wi
    #
    @5
    @6
    @7
    vw
    cv
    #
    cfv
    #
    cfv
    #
    @6
    @7
    vu
    cv
    #
    cfv
    #
    cfv
    #
    wceq
    #
    vn
    cI
    wral
    #
    vi
    cc0
    @23
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    @6
    cS
    @23
    cgsu
    co
    #
    cfv
    #
    @6
    cZ
    @26
    cgsu
    co
    #
    cfv
    #
    wceq
    #
    vn
    cI
    wral
    #
    wi
    #
    wi
    @5
    @6
    @7
    c0
    cfv
    #
    cfv
    #
    @42
    wceq
    #
    vn
    cI
    wral
    #
    vi
    cc0
    c0
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    @6
    cS
    c0
    cgsu
    co
    #
    cfv
    #
    @6
    cZ
    c0
    cgsu
    co
    #
    cfv
    #
    wceq
    #
    vn
    cI
    wral
    #
    wi
    #
    wi
    @5
    @6
    @7
    vx
    cv
    #
    cfv
    #
    cfv
    #
    @6
    @7
    vy
    cv
    #
    cfv
    #
    cfv
    #
    wceq
    #
    vn
    cI
    wral
    #
    vi
    cc0
    @55
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    @6
    cS
    @55
    cgsu
    co
    #
    cfv
    #
    @6
    cZ
    @58
    cgsu
    co
    #
    cfv
    #
    wceq
    #
    vn
    cI
    wral
    #
    wi
    #
    wi
    @5
    @6
    @7
    @55
    vb
    cv
    #
    cs1
    cconcat
    co
    #
    cfv
    #
    cfv
    #
    @6
    @7
    @58
    vp
    cv
    #
    cs1
    cconcat
    co
    #
    cfv
    #
    cfv
    #
    wceq
    #
    vn
    cI
    wral
    #
    vi
    cc0
    @74
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    @6
    cS
    @74
    cgsu
    co
    #
    cfv
    #
    @6
    cZ
    @78
    cgsu
    co
    #
    cfv
    #
    wceq
    #
    vn
    cI
    wral
    #
    wi
    #
    wi
    @5
    @22
    wi
    @5
    @25
    @11
    wceq
    #
    vn
    cI
    wral
    #
    vi
    @32
    wral
    #
    @35
    @19
    wceq
    #
    vn
    cI
    wral
    #
    wi
    #
    wi
    vw
    vx
    vb
    vu
    vy
    cW
    cU
    cB
    cP
    vp
    @23
    c0
    wceq
    #
    @26
    c0
    wceq
    #
    wa
    #
    @40
    @54
    @5
    @101
    @33
    @47
    @39
    @53
    @101
    @30
    @44
    vi
    @32
    @46
    @99
    @32
    @46
    wceq
    @100
    @99
    @31
    @45
    cc0
    cfzo
    @23
    c0
    chash
    fveq2
    oveq2d
    adantr
    @101
    @29
    @43
    vn
    cI
    @99
    @100
    @25
    @42
    @28
    @42
    @99
    @6
    @24
    @41
    @7
    @23
    c0
    fveq1
    fveq1d
    @100
    @6
    @27
    @41
    @7
    @26
    c0
    fveq1
    fveq1d
    eqeqan12d
    ralbidv
    raleqbidv
    @101
    @38
    @52
    vn
    cI
    @99
    @100
    @35
    @49
    @37
    @51
    @99
    @6
    @34
    @48
    @23
    c0
    cS
    cgsu
    oveq2
    fveq1d
    @100
    @6
    @36
    @50
    @26
    c0
    cZ
    cgsu
    oveq2
    fveq1d
    eqeqan12d
    ralbidv
    imbi12d
    imbi2d
    vw
    vx
    weq
    #
    vu
    vy
    weq
    #
    wa
    #
    @40
    @72
    @5
    @104
    @33
    @65
    @39
    @71
    @104
    @30
    @62
    vi
    @32
    @64
    @102
    @32
    @64
    wceq
    @103
    @102
    @31
    @63
    cc0
    cfzo
    @23
    @55
    chash
    fveq2
    oveq2d
    adantr
    @104
    @29
    @61
    vn
    cI
    @102
    @103
    @25
    @57
    @28
    @60
    @102
    @6
    @24
    @56
    @7
    @23
    @55
    fveq1
    fveq1d
    @103
    @6
    @27
    @59
    @7
    @26
    @58
    fveq1
    fveq1d
    eqeqan12d
    ralbidv
    raleqbidv
    @104
    @38
    @70
    vn
    cI
    @102
    @103
    @35
    @67
    @37
    @69
    @102
    @6
    @34
    @66
    @23
    @55
    cS
    cgsu
    oveq2
    fveq1d
    @103
    @6
    @36
    @68
    @26
    @58
    cZ
    cgsu
    oveq2
    fveq1d
    eqeqan12d
    ralbidv
    imbi12d
    imbi2d
    @23
    @74
    wceq
    #
    @26
    @78
    wceq
    #
    wa
    #
    @40
    @92
    @5
    @107
    @33
    @85
    @39
    @91
    @107
    @30
    @82
    vi
    @32
    @84
    @105
    @32
    @84
    wceq
    @106
    @105
    @31
    @83
    cc0
    cfzo
    @23
    @74
    chash
    fveq2
    oveq2d
    adantr
    @107
    @29
    @81
    vn
    cI
    @105
    @106
    @25
    @76
    @28
    @80
    @105
    @6
    @24
    @75
    @7
    @23
    @74
    fveq1
    fveq1d
    @106
    @6
    @27
    @79
    @7
    @26
    @78
    fveq1
    fveq1d
    eqeqan12d
    ralbidv
    raleqbidv
    @107
    @38
    @90
    vn
    cI
    @105
    @106
    @35
    @87
    @37
    @89
    @105
    @6
    @34
    @86
    @23
    @74
    cS
    cgsu
    oveq2
    fveq1d
    @106
    @6
    @36
    @88
    @26
    @78
    cZ
    cgsu
    oveq2
    fveq1d
    eqeqan12d
    ralbidv
    imbi12d
    imbi2d
    @23
    cW
    wceq
    #
    @98
    @22
    @5
    @108
    @95
    @15
    @97
    @21
    @108
    @94
    @13
    vi
    @32
    @14
    @108
    @31
    @2
    cc0
    cfzo
    @23
    cW
    chash
    fveq2
    oveq2d
    @108
    @93
    @12
    vn
    cI
    @108
    @25
    @9
    @11
    @108
    @6
    @24
    @8
    @7
    @23
    cW
    fveq1
    fveq1d
    eqeq1d
    ralbidv
    raleqbidv
    @108
    @96
    @20
    vn
    cI
    @108
    @35
    @17
    @19
    @108
    @6
    @34
    @16
    @23
    cW
    cS
    cgsu
    oveq2
    fveq1d
    eqeq1d
    ralbidv
    imbi12d
    imbi2d
    @26
    cU
    wceq
    #
    @40
    @98
    @5
    @109
    @33
    @95
    @39
    @97
    @109
    @30
    @94
    vi
    @32
    @109
    @29
    @93
    vn
    cI
    @109
    @28
    @11
    @25
    @109
    @6
    @27
    @10
    @7
    @26
    cU
    fveq1
    fveq1d
    eqeq2d
    ralbidv
    ralbidv
    @109
    @38
    @96
    vn
    cI
    @109
    @37
    @19
    @35
    @109
    @6
    @36
    @18
    @26
    cU
    cZ
    cgsu
    oveq2
    fveq1d
    eqeq2d
    ralbidv
    imbi12d
    imbi2d
    @5
    @53
    @47
    @5
    @53
    @6
    cid
    cN
    cres
    #
    cfv
    #
    @6
    cid
    cM
    cres
    #
    cfv
    #
    wceq
    #
    vn
    cI
    wral
    @5
    @114
    vn
    cI
    @5
    @6
    cI
    wcel
    #
    wa
    #
    @111
    @6
    @113
    @116
    @6
    cN
    wcel
    #
    @111
    @6
    wceq
    @115
    @117
    @5
    cI
    cN
    cM
    cin
    #
    wceq
    #
    @115
    @117
    wi
    gsmsymgreq.i
    @119
    @115
    @117
    @6
    cM
    wcel
    #
    wa
    #
    @117
    @119
    @115
    @6
    @118
    wcel
    @121
    cI
    @118
    @6
    eleq2
    @6
    cN
    cM
    elin
    syl6bb
    #
    @117
    @120
    simpl
    syl6bi
    ax-mp
    adantl
    cN
    @6
    fvresi
    syl
    @116
    @120
    @113
    @6
    wceq
    @115
    @120
    @5
    @119
    @115
    @120
    wi
    gsmsymgreq.i
    @119
    @115
    @121
    @120
    @122
    @117
    @120
    simpr
    syl6bi
    ax-mp
    adantl
    cM
    @6
    fvresi
    syl
    eqtr4d
    ralrimiva
    @5
    @52
    @114
    vn
    cI
    @5
    @49
    @111
    @51
    @113
    @5
    @6
    @48
    @110
    @5
    @110
    cS
    c0g
    cfv
    #
    @48
    @3
    @110
    @123
    wceq
    @4
    cN
    cS
    cfn
    gsmsymgrfix.s
    symgid
    adantr
    cS
    @123
    @123
    eqid
    gsum0
    syl6reqr
    fveq1d
    @5
    @6
    @50
    @112
    @5
    @112
    cZ
    c0g
    cfv
    #
    @50
    @4
    @112
    @124
    wceq
    @3
    cM
    cZ
    cfn
    gsmsymgreq.z
    symgid
    adantl
    cZ
    @124
    @124
    eqid
    gsum0
    syl6reqr
    fveq1d
    eqeq12d
    ralbidv
    mpbird
    a1d
    @55
    @0
    wcel
    @73
    cB
    wcel
    wa
    @58
    @1
    wcel
    @77
    cP
    wcel
    wa
    @63
    @58
    chash
    cfv
    wceq
    w3a
    #
    @5
    @72
    @92
    @5
    @125
    @72
    @92
    wi
    cB
    @73
    cP
    @77
    cS
    vi
    vn
    cI
    cM
    cN
    @55
    @58
    cZ
    gsmsymgrfix.s
    gsmsymgrfix.b
    gsmsymgreq.z
    gsmsymgreq.p
    gsmsymgreq.i
    gsmsymgreqlem2
    expcom
    a2d
    wrd2ind
    impcom
end
