include "cwwlksn.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wfo.mm"
include "cvv.mm"
include "cn0.mm"
include "cword.mm"
include "w3a.mm"
include "wwlknbp.mm"
include "simp2.mm"
include "wwlksnextfun.mm"
include "3syl.mm"
include "clsw.mm"
include "cpr.mm"
include "wa.mm"
include "preq2.mm"
include "eleq1d.mm"
include "elrab2.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "cop.mm"
include "csubstr.mm"
include "crab.mm"
include "wex.mm"
include "cs1.mm"
include "cconcat.mm"
include "wwlksnext.mm"
include "3expb.mm"
include "wi.mm"
include "chash.mm"
include "cfzo.mm"
include "s1cl.mm"
include "swrdccat1.mm"
include "sylan2.mm"
include "ex.mm"
include "adantr.mm"
include "wb.mm"
include "opeq2.mm"
include "eqcoms.mm"
include "oveq2d.mm"
include "eqeq1d.mm"
include "adantl.mm"
include "sylibrd.mm"
include "3adant3.mm"
include "wwlknp.mm"
include "syl11.mm"
include "impcom.mm"
include "lswccats1.mm"
include "eqcomd.mm"
include "3ad2ant3.mm"
include "syl.mm"
include "imp.mm"
include "preq2d.mm"
include "biimpd.mm"
include "impr.mm"
include "jca32.mm"
include "ovexd.mm"
include "eleq1.mm"
include "oveq1.mm"
include "fveq2.mm"
include "anbi12d.mm"
include "eqeq2d.mm"
include "bicomd.mm"
include "spcimedv.mm"
include "mp2and.mm"
include "elrab.mm"
include "anbi1i.mm"
include "exbii.mm"
include "sylibr.mm"
include "df-rex.mm"
include "wwlksnextwrd.mm"
include "rexeqdv.mm"
include "mpbird.mm"
include "fvex.mm"
include "fvmpt.mm"
include "rexbiia.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "dffo3.mm"
include "sylanbrc.mm"

theorem wwlksnextsur
  let vw: setvar w
  let vt: setvar t
  let cD: class D
  let cR: class R
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let vi: setvar i
  let vd: setvar d
  let vx: setvar x
  let vr: setvar r
  assume wwlksnextbij0.v: |- V = ( Vtx ` G )
  assume wwlksnextbij0.e: |- E = ( Edg ` G )
  assume wwlksnextbij0.d: |- D = { w e. Word V | ( ( # ` w ) = ( N + 2 ) /\ ( w substr <. 0 , ( N + 1 ) >. ) = W /\ { ( lastS ` W ) , ( lastS ` w ) } e. E ) }
  assume wwlksnextbij.r: |- R = { n e. V | { ( lastS ` W ) , n } e. E }
  assume wwlksnextbij.f: |- F = ( t e. D |-> ( lastS ` t ) )

  disjoint G w
  disjoint N w
  disjoint W w
  disjoint D t
  disjoint E n
  disjoint E w
  disjoint N t
  disjoint t w
  disjoint R t
  disjoint V n
  disjoint V w
  disjoint W n
  disjoint n t
  disjoint N n
  disjoint n w
  disjoint G i
  disjoint i w
  disjoint N i
  disjoint D d
  disjoint D x
  disjoint d x
  disjoint F d
  disjoint F x
  disjoint N d
  disjoint N x
  disjoint d t
  disjoint d w
  disjoint t x
  disjoint w x
  disjoint D r
  disjoint d r
  disjoint E d
  disjoint F r
  disjoint G d
  disjoint G r
  disjoint N r
  disjoint d n
  disjoint n r
  disjoint r t
  disjoint r w
  disjoint R d
  disjoint R r
  disjoint V d
  disjoint W d
  disjoint W i
  disjoint W r
  disjoint d i
  disjoint i r
  assert |- ( W e. ( N WWalksN G ) -> F : D -onto-> R )

  proof
    cW
    cN
    cG
    cwwlksn
    co
    wcel
    #
    cD
    cR
    cF
    wf
    #
    vr
    cv
    #
    vd
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vd
    cD
    wrex
    #
    vr
    cR
    wral
    cD
    cR
    cF
    wfo
    @0
    cG
    cvv
    wcel
    #
    cN
    cn0
    wcel
    #
    cW
    cV
    cword
    #
    wcel
    #
    w3a
    #
    @8
    @1
    cG
    cN
    cV
    cW
    wwlksnextbij0.v
    wwlknbp
    #
    @7
    @8
    @10
    simp2
    vw
    vt
    cD
    cR
    vn
    cE
    cF
    cG
    cN
    cV
    cW
    wwlksnextbij0.v
    wwlksnextbij0.e
    wwlksnextbij0.d
    wwlksnextbij.r
    wwlksnextbij.f
    wwlksnextfun
    3syl
    @0
    @6
    vr
    cR
    @2
    cR
    wcel
    @0
    @2
    cV
    wcel
    #
    cW
    clsw
    cfv
    #
    @2
    cpr
    #
    cE
    wcel
    #
    wa
    #
    @6
    @14
    vn
    cv
    #
    cpr
    #
    cE
    wcel
    @16
    vn
    @2
    cV
    cR
    @18
    @2
    wceq
    @19
    @15
    cE
    @18
    @2
    @14
    preq2
    eleq1d
    wwlksnextbij.r
    elrab2
    @0
    @17
    wa
    #
    @2
    @3
    clsw
    cfv
    #
    wceq
    #
    vd
    cD
    wrex
    #
    @6
    @20
    @23
    @22
    vd
    vw
    cv
    #
    cc0
    cN
    c1
    caddc
    co
    #
    cop
    #
    csubstr
    co
    #
    cW
    wceq
    #
    @14
    @24
    clsw
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    wa
    #
    vw
    @25
    cG
    cwwlksn
    co
    #
    crab
    #
    wrex
    #
    @20
    @3
    @34
    wcel
    #
    @22
    wa
    #
    vd
    wex
    #
    @35
    @20
    @3
    @33
    wcel
    #
    @3
    @26
    csubstr
    co
    #
    cW
    wceq
    #
    @14
    @21
    cpr
    #
    cE
    wcel
    #
    wa
    #
    wa
    #
    @22
    wa
    #
    vd
    wex
    #
    @38
    @20
    cW
    @2
    cs1
    #
    cconcat
    co
    #
    @33
    wcel
    #
    @49
    @26
    csubstr
    co
    #
    cW
    wceq
    #
    @14
    @49
    clsw
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    wa
    #
    wa
    #
    @2
    @53
    wceq
    #
    @47
    @20
    @50
    @52
    @55
    @0
    @13
    @16
    @50
    @2
    cW
    cE
    cG
    cN
    cV
    wwlksnextbij0.v
    wwlksnextbij0.e
    wwlksnext
    3expb
    @17
    @0
    @52
    @13
    @0
    @52
    wi
    @16
    @10
    cW
    chash
    cfv
    #
    @25
    wceq
    #
    vi
    cv
    #
    cW
    cfv
    @61
    c1
    caddc
    co
    cW
    cfv
    cpr
    cE
    wcel
    vi
    cc0
    cN
    cfzo
    co
    wral
    #
    w3a
    @13
    @52
    @0
    @10
    @60
    @13
    @52
    wi
    @62
    @10
    @60
    wa
    @13
    @49
    cc0
    @59
    cop
    #
    csubstr
    co
    #
    cW
    wceq
    #
    @52
    @10
    @13
    @65
    wi
    @60
    @10
    @13
    @65
    @13
    @10
    @48
    @9
    wcel
    @65
    @2
    cV
    s1cl
    cV
    cW
    @48
    swrdccat1
    sylan2
    ex
    adantr
    @60
    @52
    @65
    wb
    @10
    @60
    @51
    @64
    cW
    @60
    @26
    @63
    @49
    csubstr
    @26
    @63
    wceq
    @25
    @59
    @25
    @59
    cc0
    opeq2
    eqcoms
    oveq2d
    eqeq1d
    adantl
    sylibrd
    3adant3
    vi
    cE
    cG
    cN
    cV
    cW
    wwlksnextbij0.v
    wwlksnextbij0.e
    wwlknp
    syl11
    adantr
    impcom
    @0
    @13
    @16
    @55
    @0
    @13
    wa
    #
    @16
    @55
    @66
    @15
    @54
    cE
    @66
    @2
    @53
    @14
    @0
    @13
    @58
    @0
    @11
    @13
    @58
    wi
    #
    @12
    @10
    @7
    @67
    @8
    @10
    @13
    @58
    @10
    @13
    wa
    @53
    @2
    @2
    cV
    cW
    lswccats1
    eqcomd
    ex
    3ad2ant3
    #
    syl
    imp
    preq2d
    eleq1d
    biimpd
    impr
    jca32
    @17
    @0
    @58
    @13
    @0
    @58
    wi
    @16
    @11
    @13
    @58
    @0
    @68
    @12
    syl11
    adantr
    impcom
    @20
    @46
    @57
    @58
    wa
    #
    vd
    @49
    cvv
    @20
    cW
    @48
    cconcat
    ovexd
    @20
    @3
    @49
    wceq
    #
    wa
    @69
    @46
    @70
    @69
    @46
    wb
    @20
    @70
    @46
    @69
    @70
    @45
    @57
    @22
    @58
    @70
    @39
    @50
    @44
    @56
    @3
    @49
    @33
    eleq1
    @70
    @41
    @52
    @43
    @55
    @70
    @40
    @51
    cW
    @3
    @49
    @26
    csubstr
    oveq1
    eqeq1d
    @70
    @42
    @54
    cE
    @70
    @21
    @53
    @14
    @3
    @49
    clsw
    fveq2
    #
    preq2d
    eleq1d
    anbi12d
    anbi12d
    @70
    @21
    @53
    @2
    @71
    eqeq2d
    anbi12d
    bicomd
    adantl
    biimpd
    spcimedv
    mp2and
    @37
    @46
    vd
    @36
    @45
    @22
    @32
    @44
    vw
    @3
    @33
    @24
    @3
    wceq
    #
    @28
    @41
    @31
    @43
    @72
    @27
    @40
    cW
    @24
    @3
    @26
    csubstr
    oveq1
    eqeq1d
    @72
    @30
    @42
    cE
    @72
    @29
    @21
    @14
    @24
    @3
    clsw
    fveq2
    preq2d
    eleq1d
    anbi12d
    elrab
    anbi1i
    exbii
    sylibr
    @22
    vd
    @34
    df-rex
    sylibr
    @20
    @22
    vd
    cD
    @34
    @0
    cD
    @34
    wceq
    @17
    vw
    cD
    cE
    cG
    cN
    cV
    cW
    wwlksnextbij0.v
    wwlksnextbij0.e
    wwlksnextbij0.d
    wwlksnextwrd
    adantr
    rexeqdv
    mpbird
    @5
    @22
    vd
    cD
    @3
    cD
    wcel
    @4
    @21
    @2
    vt
    @3
    vt
    cv
    #
    clsw
    cfv
    @21
    cD
    cF
    @73
    @3
    clsw
    fveq2
    wwlksnextbij.f
    @3
    clsw
    fvex
    fvmpt
    eqeq2d
    rexbiia
    sylibr
    sylan2b
    ralrimiva
    vd
    vr
    cD
    cR
    cF
    dffo3
    sylanbrc
end
