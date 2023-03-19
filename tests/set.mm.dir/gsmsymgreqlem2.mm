include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cword.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "wral.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cgsu.mm"
include "wi.mm"
include "cs1.mm"
include "cconcat.mm"
include "wb.mm"
include "csn.mm"
include "cun.mm"
include "c1.mm"
include "caddc.mm"
include "ccatws1len.mm"
include "adantr.mm"
include "3ad2ant1.mm"
include "oveq2d.mm"
include "cuz.mm"
include "cn0.mm"
include "lencl.mm"
include "elnn0uz.mm"
include "sylib.mm"
include "fzosplitsn.mm"
include "syl.mm"
include "eqtrd.mm"
include "raleqdv.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "ralunsn.mm"
include "simpl.mm"
include "simpr.mm"
include "ccats1val1.mm"
include "syl3anc.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "biimpd.mm"
include "3ad2ant3.mm"
include "imp.mm"
include "ralbidva.mm"
include "eqidd.mm"
include "3jca.mm"
include "ccats1val2.mm"
include "df-3an.mm"
include "biimpri.mm"
include "3adant1.mm"
include "anbi12d.mm"
include "3bitrd.mm"
include "ad2antlr.mm"
include "pm3.35.mm"
include "weq.mm"
include "cbvralv.mm"
include "simp-4l.mm"
include "simp-4r.mm"
include "anim1i.mm"
include "gsmsymgreqlem1.mm"
include "syl21anc.mm"
include "ex.mm"
include "ralimdva.mm"
include "expcom.mm"
include "sylbi.mm"
include "com23.mm"
include "impancom.mm"
include "com13.mm"
include "sylbid.mm"

theorem gsmsymgreqlem2
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vn: setvar n
  let cI: class I
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let cK: class K
  let cW: class W
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let vj: setvar j
  assume gsmsymgrfix.s: |- S = ( SymGrp ` N )
  assume gsmsymgrfix.b: |- B = ( Base ` S )
  assume gsmsymgreq.z: |- Z = ( SymGrp ` M )
  assume gsmsymgreq.p: |- P = ( Base ` Z )
  assume gsmsymgreq.i: |- I = ( N i^i M )

  disjoint B i
  disjoint N i
  disjoint P i
  disjoint I n
  disjoint X n
  disjoint C n
  disjoint R n
  disjoint S n
  disjoint Y n
  disjoint Z n
  disjoint B n
  disjoint C i
  disjoint i n
  disjoint I i
  disjoint M n
  disjoint N n
  disjoint P n
  disjoint R i
  disjoint X i
  disjoint Y i
  disjoint K i
  disjoint W i
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
  disjoint J n
  disjoint C j
  disjoint i j
  disjoint j n
  disjoint I j
  disjoint R j
  disjoint S j
  disjoint X j
  disjoint Y j
  disjoint Z j
  assert |- ( ( ( N e. Fin /\ M e. Fin ) /\ ( ( X e. Word B /\ C e. B ) /\ ( Y e. Word P /\ R e. P ) /\ ( # ` X ) = ( # ` Y ) ) ) -> ( ( A. i e. ( 0 ..^ ( # ` X ) ) A. n e. I ( ( X ` i ) ` n ) = ( ( Y ` i ) ` n ) -> A. n e. I ( ( S gsum X ) ` n ) = ( ( Z gsum Y ) ` n ) ) -> ( A. i e. ( 0 ..^ ( # ` ( X ++ <" C "> ) ) ) A. n e. I ( ( ( X ++ <" C "> ) ` i ) ` n ) = ( ( ( Y ++ <" R "> ) ` i ) ` n ) -> A. n e. I ( ( S gsum ( X ++ <" C "> ) ) ` n ) = ( ( Z gsum ( Y ++ <" R "> ) ) ` n ) ) ) )

  proof
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
    cX
    cB
    cword
    wcel
    #
    cC
    cB
    wcel
    #
    wa
    #
    cY
    cP
    cword
    wcel
    #
    cR
    cP
    wcel
    #
    wa
    #
    cX
    chash
    cfv
    #
    cY
    chash
    cfv
    #
    wceq
    #
    w3a
    #
    wa
    #
    vn
    cv
    #
    vi
    cv
    #
    cX
    cfv
    #
    cfv
    #
    @14
    @15
    cY
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
    @9
    cfzo
    co
    #
    wral
    #
    @14
    cS
    cX
    cgsu
    co
    #
    cfv
    #
    @14
    cZ
    cY
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
    @14
    @15
    cX
    cC
    cs1
    cconcat
    co
    #
    cfv
    #
    cfv
    #
    @14
    @15
    cY
    cR
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
    @31
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    @14
    cS
    @31
    cgsu
    co
    cfv
    @14
    cZ
    @34
    cgsu
    co
    cfv
    wceq
    #
    vn
    cI
    wral
    #
    wi
    @13
    @30
    wa
    @41
    @23
    @14
    cC
    cfv
    #
    @14
    cR
    cfv
    #
    wceq
    #
    vn
    cI
    wral
    #
    wa
    #
    @43
    @12
    @41
    @48
    wb
    @2
    @30
    @12
    @41
    @38
    vi
    @22
    @9
    csn
    cun
    #
    wral
    #
    @38
    vi
    @22
    wral
    #
    @14
    @9
    @31
    cfv
    #
    cfv
    #
    @14
    @9
    @34
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
    wa
    #
    @48
    @12
    @38
    vi
    @40
    @49
    @12
    @40
    cc0
    @9
    c1
    caddc
    co
    #
    cfzo
    co
    #
    @49
    @12
    @39
    @59
    cc0
    cfzo
    @5
    @8
    @39
    @59
    wceq
    #
    @11
    @3
    @61
    @4
    cB
    cX
    cC
    ccatws1len
    adantr
    3ad2ant1
    oveq2d
    @5
    @8
    @60
    @49
    wceq
    #
    @11
    @5
    @9
    cc0
    cuz
    cfv
    wcel
    #
    @62
    @3
    @63
    @4
    @3
    @9
    cn0
    wcel
    #
    @63
    cB
    cX
    lencl
    #
    @9
    elnn0uz
    sylib
    adantr
    cc0
    @9
    fzosplitsn
    syl
    3ad2ant1
    eqtrd
    raleqdv
    @12
    @64
    @50
    @58
    wb
    @5
    @8
    @64
    @11
    @3
    @64
    @4
    @65
    adantr
    3ad2ant1
    @38
    @57
    vi
    @22
    @9
    cn0
    @15
    @9
    wceq
    #
    @37
    @56
    vn
    cI
    @66
    @33
    @53
    @36
    @55
    @66
    @14
    @32
    @52
    @15
    @9
    @31
    fveq2
    fveq1d
    @66
    @14
    @35
    @54
    @15
    @9
    @34
    fveq2
    fveq1d
    eqeq12d
    ralbidv
    ralunsn
    syl
    @12
    @51
    @23
    @57
    @47
    @12
    @38
    @21
    vi
    @22
    @12
    @15
    @22
    wcel
    #
    wa
    #
    @37
    @20
    vn
    cI
    @68
    @33
    @17
    @36
    @19
    @68
    @14
    @32
    @16
    @68
    @3
    @4
    @67
    @32
    @16
    wceq
    @12
    @3
    @67
    @5
    @8
    @3
    @11
    @3
    @4
    simpl
    #
    3ad2ant1
    adantr
    @12
    @4
    @67
    @5
    @8
    @4
    @11
    @3
    @4
    simpr
    #
    3ad2ant1
    adantr
    @12
    @67
    simpr
    cC
    @15
    cB
    cX
    ccats1val1
    syl3anc
    fveq1d
    @68
    @14
    @35
    @18
    @68
    @6
    @7
    @15
    cc0
    @10
    cfzo
    co
    #
    wcel
    #
    @35
    @18
    wceq
    @6
    @7
    @5
    @11
    @67
    simpl2l
    @6
    @7
    @5
    @11
    @67
    simpl2r
    @12
    @67
    @72
    @11
    @5
    @67
    @72
    wi
    @8
    @11
    @67
    @72
    @11
    @22
    @71
    @15
    @9
    @10
    cc0
    cfzo
    oveq2
    eleq2d
    biimpd
    3ad2ant3
    imp
    cR
    @15
    cP
    cY
    ccats1val1
    syl3anc
    fveq1d
    eqeq12d
    ralbidv
    ralbidva
    @12
    @56
    @46
    vn
    cI
    @12
    @53
    @44
    @55
    @45
    @12
    @14
    @52
    cC
    @12
    @3
    @4
    @9
    @9
    wceq
    #
    w3a
    #
    @52
    cC
    wceq
    @5
    @8
    @74
    @11
    @5
    @3
    @4
    @73
    @69
    @70
    @5
    @9
    eqidd
    3jca
    3ad2ant1
    cC
    @9
    cB
    cX
    ccats1val2
    syl
    fveq1d
    @12
    @6
    @7
    @11
    w3a
    #
    @55
    @45
    wceq
    @8
    @11
    @75
    @5
    @75
    @8
    @11
    wa
    @6
    @7
    @11
    df-3an
    biimpri
    3adant1
    @75
    @14
    @54
    cR
    cR
    @9
    cP
    cY
    ccats1val2
    fveq1d
    syl
    eqeq12d
    ralbidv
    anbi12d
    3bitrd
    ad2antlr
    @13
    @30
    @48
    @43
    wi
    @48
    @30
    @13
    @43
    @23
    @30
    @47
    @13
    @43
    wi
    #
    @23
    @30
    wa
    @29
    @47
    @76
    wi
    @23
    @29
    pm3.35
    @29
    @13
    @47
    @43
    @29
    vj
    cv
    #
    @24
    cfv
    #
    @77
    @26
    cfv
    #
    wceq
    #
    vj
    cI
    wral
    #
    @13
    @47
    @43
    wi
    #
    wi
    @28
    @80
    vn
    vj
    cI
    vn
    vj
    weq
    @25
    @78
    @27
    @79
    @14
    @77
    @24
    fveq2
    @14
    @77
    @26
    fveq2
    eqeq12d
    cbvralv
    @13
    @81
    @82
    @13
    @81
    wa
    #
    @46
    @42
    vn
    cI
    @83
    @14
    cI
    wcel
    #
    wa
    #
    @46
    @42
    @85
    @46
    wa
    @0
    @1
    @84
    w3a
    #
    @12
    @81
    @46
    wa
    #
    @42
    @85
    @86
    @46
    @85
    @0
    @1
    @84
    @0
    @1
    @12
    @81
    @84
    simp-4l
    @0
    @1
    @12
    @81
    @84
    simp-4r
    @83
    @84
    simpr
    3jca
    adantr
    @2
    @12
    @81
    @84
    @46
    simp-4r
    @85
    @81
    @46
    @83
    @81
    @84
    @13
    @81
    simpr
    adantr
    anim1i
    @86
    @12
    wa
    @87
    @42
    cB
    cC
    cP
    cR
    cS
    vj
    cI
    @14
    cM
    cN
    cX
    cY
    cZ
    gsmsymgrfix.s
    gsmsymgrfix.b
    gsmsymgreq.z
    gsmsymgreq.p
    gsmsymgreq.i
    gsmsymgreqlem1
    imp
    syl21anc
    ex
    ralimdva
    expcom
    sylbi
    com23
    syl
    impancom
    com13
    imp
    sylbid
    ex
end
