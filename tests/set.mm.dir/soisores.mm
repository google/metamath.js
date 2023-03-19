include "wor.mm"
include "wa.mm"
include "wf.mm"
include "wss.mm"
include "cima.mm"
include "cres.mm"
include "wiso.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wcel.mm"
include "isorel.mm"
include "wb.mm"
include "fvres.mm"
include "breqan12d.mm"
include "adantl.mm"
include "bitrd.mm"
include "biimpd.mm"
include "ralrimivva.mm"
include "w3a.mm"
include "wf1o.mm"
include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "weq.mm"
include "ffn.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "fnssres.mm"
include "syl2anc.mm"
include "3adant3.mm"
include "df-ima.mm"
include "eqcomi.mm"
include "a1i.mm"
include "eqeqan12d.mm"
include "wo.mm"
include "wn.mm"
include "simprl.mm"
include "simpl3.mm"
include "breq1.mm"
include "fveq2.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "breq2.mm"
include "breq2d.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "orim12d.mm"
include "con3d.mm"
include "simpl1r.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "sseldd.mm"
include "ffvelrnd.mm"
include "sotrieq.mm"
include "syl12anc.mm"
include "simpl1l.mm"
include "3imtr4d.mm"
include "sylbid.mm"
include "dff1o6.mm"
include "syl3anbrc.mm"
include "sotric.mm"
include "impbid.mm"
include "bitr4d.mm"
include "df-isom.mm"
include "sylanbrc.mm"
include "3expia.mm"
include "impbid2.mm"

theorem soisores
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let vw: setvar w
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B w
  disjoint B z
  disjoint C w
  disjoint C z
  disjoint F w
  disjoint F z
  disjoint R w
  disjoint R z
  disjoint S w
  disjoint S z
  assert |- ( ( ( R Or B /\ S Or C ) /\ ( F : B --> C /\ A C_ B ) ) -> ( ( F |` A ) Isom R , S ( A , ( F " A ) ) <-> A. x e. A A. y e. A ( x R y -> ( F ` x ) S ( F ` y ) ) ) )

  proof
    cB
    cR
    wor
    #
    cC
    cS
    wor
    #
    wa
    #
    cB
    cC
    cF
    wf
    #
    cA
    cB
    wss
    #
    wa
    #
    wa
    #
    cA
    cF
    cA
    cima
    #
    cR
    cS
    cF
    cA
    cres
    #
    wiso
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @10
    cF
    cfv
    #
    @11
    cF
    cfv
    #
    cS
    wbr
    #
    wi
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    @9
    @16
    vx
    vy
    cA
    cA
    @9
    @10
    cA
    wcel
    #
    @11
    cA
    wcel
    #
    wa
    #
    wa
    #
    @12
    @15
    @21
    @12
    @10
    @8
    cfv
    #
    @11
    @8
    cfv
    #
    cS
    wbr
    #
    @15
    cA
    @7
    @10
    @11
    cR
    cS
    @8
    isorel
    @20
    @24
    @15
    wb
    @9
    @18
    @19
    @22
    @13
    @23
    @14
    cS
    @10
    cA
    cF
    fvres
    @11
    cA
    cF
    fvres
    breqan12d
    adantl
    bitrd
    biimpd
    ralrimivva
    @2
    @5
    @17
    @9
    @2
    @5
    @17
    w3a
    #
    cA
    @7
    @8
    wf1o
    #
    vz
    cv
    #
    vw
    cv
    #
    cR
    wbr
    #
    @27
    @8
    cfv
    #
    @28
    @8
    cfv
    #
    cS
    wbr
    #
    wb
    #
    vw
    cA
    wral
    vz
    cA
    wral
    @9
    @25
    @8
    cA
    wfn
    #
    @8
    crn
    #
    @7
    wceq
    #
    @30
    @31
    wceq
    #
    vz
    vw
    weq
    #
    wi
    #
    vw
    cA
    wral
    vz
    cA
    wral
    @26
    @2
    @5
    @34
    @17
    @6
    cF
    cB
    wfn
    #
    @4
    @34
    @3
    @40
    @2
    @4
    cB
    cC
    cF
    ffn
    ad2antrl
    @2
    @3
    @4
    simprr
    cB
    cA
    cF
    fnssres
    syl2anc
    3adant3
    @36
    @25
    @7
    @35
    cF
    cA
    df-ima
    eqcomi
    a1i
    @25
    @39
    vz
    vw
    cA
    cA
    @25
    @27
    cA
    wcel
    #
    @28
    cA
    wcel
    #
    wa
    #
    wa
    #
    @37
    @27
    cF
    cfv
    #
    @28
    cF
    cfv
    #
    wceq
    #
    @38
    @43
    @37
    @47
    wb
    @25
    @41
    @42
    @30
    @45
    @31
    @46
    @27
    cA
    cF
    fvres
    #
    @28
    cA
    cF
    fvres
    #
    eqeqan12d
    adantl
    @44
    @45
    @46
    cS
    wbr
    #
    @46
    @45
    cS
    wbr
    #
    wo
    #
    wn
    #
    @29
    @28
    @27
    cR
    wbr
    #
    wo
    #
    wn
    #
    @47
    @38
    @44
    @55
    @52
    @44
    @29
    @50
    @54
    @51
    @44
    @41
    @42
    @17
    @29
    @50
    wi
    #
    @25
    @41
    @42
    simprl
    #
    @25
    @41
    @42
    simprr
    #
    @2
    @5
    @17
    @43
    simpl3
    #
    @16
    @57
    @27
    @11
    cR
    wbr
    #
    @45
    @14
    cS
    wbr
    #
    wi
    vx
    vy
    @27
    @28
    cA
    cA
    vx
    vz
    weq
    #
    @12
    @61
    @15
    @62
    @10
    @27
    @11
    cR
    breq1
    @63
    @13
    @45
    @14
    cS
    @10
    @27
    cF
    fveq2
    breq1d
    imbi12d
    vy
    vw
    weq
    #
    @61
    @29
    @62
    @50
    @11
    @28
    @27
    cR
    breq2
    @64
    @14
    @46
    @45
    cS
    @11
    @28
    cF
    fveq2
    breq2d
    imbi12d
    rspc2va
    syl21anc
    #
    @44
    @42
    @41
    @17
    @54
    @51
    wi
    #
    @59
    @58
    @60
    @16
    @66
    @28
    @11
    cR
    wbr
    #
    @46
    @14
    cS
    wbr
    #
    wi
    vx
    vy
    @28
    @27
    cA
    cA
    vx
    vw
    weq
    #
    @12
    @67
    @15
    @68
    @10
    @28
    @11
    cR
    breq1
    @69
    @13
    @46
    @14
    cS
    @10
    @28
    cF
    fveq2
    breq1d
    imbi12d
    vy
    vz
    weq
    #
    @67
    @54
    @68
    @51
    @11
    @27
    @28
    cR
    breq2
    @70
    @14
    @45
    @46
    cS
    @11
    @27
    cF
    fveq2
    breq2d
    imbi12d
    rspc2va
    syl21anc
    #
    orim12d
    con3d
    @44
    @1
    @45
    cC
    wcel
    #
    @46
    cC
    wcel
    #
    @47
    @53
    wb
    @0
    @1
    @5
    @17
    @43
    simpl1r
    #
    @44
    cB
    cC
    @27
    cF
    @3
    @4
    @2
    @17
    @43
    simpl2l
    #
    @44
    cA
    cB
    @27
    @3
    @4
    @2
    @17
    @43
    simpl2r
    #
    @58
    sseldd
    #
    ffvelrnd
    #
    @44
    cB
    cC
    @28
    cF
    @75
    @44
    cA
    cB
    @28
    @76
    @59
    sseldd
    #
    ffvelrnd
    #
    cC
    @45
    @46
    cS
    sotrieq
    syl12anc
    @44
    @0
    @27
    cB
    wcel
    #
    @28
    cB
    wcel
    #
    @38
    @56
    wb
    @0
    @1
    @5
    @17
    @43
    simpl1l
    #
    @77
    @79
    cB
    @27
    @28
    cR
    sotrieq
    syl12anc
    3imtr4d
    sylbid
    ralrimivva
    vz
    vw
    cA
    @7
    @8
    dff1o6
    syl3anbrc
    @25
    @33
    vz
    vw
    cA
    cA
    @44
    @29
    @50
    @32
    @44
    @29
    @50
    @65
    @44
    @47
    @51
    wo
    #
    wn
    #
    @38
    @54
    wo
    #
    wn
    #
    @50
    @29
    @44
    @86
    @84
    @44
    @38
    @47
    @54
    @51
    @38
    @47
    wi
    @44
    @27
    @28
    cF
    fveq2
    a1i
    @71
    orim12d
    con3d
    @44
    @1
    @72
    @73
    @50
    @85
    wb
    @74
    @78
    @80
    cC
    @45
    @46
    cS
    sotric
    syl12anc
    @44
    @0
    @81
    @82
    @29
    @87
    wb
    @83
    @77
    @79
    cB
    @27
    @28
    cR
    sotric
    syl12anc
    3imtr4d
    impbid
    @43
    @32
    @50
    wb
    @25
    @41
    @42
    @30
    @45
    @31
    @46
    cS
    @48
    @49
    breqan12d
    adantl
    bitr4d
    ralrimivva
    vz
    vw
    cA
    @7
    cR
    cS
    @8
    df-isom
    sylanbrc
    3expia
    impbid2
end
