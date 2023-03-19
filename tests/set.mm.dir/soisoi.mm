include "wor.mm"
include "wpo.mm"
include "wa.mm"
include "wfo.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wf1o.mm"
include "wb.mm"
include "wiso.mm"
include "wf1.mm"
include "wf.mm"
include "wceq.mm"
include "weq.mm"
include "simprl.mm"
include "fof.mm"
include "syl.mm"
include "wcel.mm"
include "wn.mm"
include "wo.mm"
include "simpll.mm"
include "sotrieq.mm"
include "con2bid.mm"
include "sylan.mm"
include "simprr.mm"
include "breq1.mm"
include "fveq2.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "breq2.mm"
include "breq2d.mm"
include "rspc2va.mm"
include "ancoms.mm"
include "simpllr.mm"
include "simplrl.mm"
include "ffvelrnd.mm"
include "poirr.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "syl2anc.mm"
include "con2d.mm"
include "syld.mm"
include "ancom2s.mm"
include "jaod.mm"
include "sylbird.mm"
include "con4d.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"
include "df-f1o.mm"
include "sotric.mm"
include "po2nr.mm"
include "imnan.mm"
include "sylibr.mm"
include "syl12anc.mm"
include "impcon4bid.mm"
include "df-isom.mm"

theorem soisoi
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cH: class H
  let va: setvar a
  let vb: setvar b

  disjoint R x
  disjoint R y
  disjoint x y
  disjoint S x
  disjoint S y
  disjoint H x
  disjoint H y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint R a
  disjoint R b
  disjoint a x
  disjoint b x
  disjoint a y
  disjoint b y
  disjoint a b
  disjoint S a
  disjoint S b
  disjoint H a
  disjoint H b
  disjoint A a
  disjoint A b
  disjoint B a
  disjoint B b
  assert |- ( ( ( R Or A /\ S Po B ) /\ ( H : A -onto-> B /\ A. x e. A A. y e. A ( x R y -> ( H ` x ) S ( H ` y ) ) ) ) -> H Isom R , S ( A , B ) )

  proof
    cA
    cR
    wor
    #
    cB
    cS
    wpo
    #
    wa
    #
    cA
    cB
    cH
    wfo
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
    @4
    cH
    cfv
    #
    @5
    cH
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
    wa
    #
    wa
    #
    cA
    cB
    cH
    wf1o
    #
    va
    cv
    #
    vb
    cv
    #
    cR
    wbr
    #
    @15
    cH
    cfv
    #
    @16
    cH
    cfv
    #
    cS
    wbr
    #
    wb
    #
    vb
    cA
    wral
    va
    cA
    wral
    cA
    cB
    cR
    cS
    cH
    wiso
    @13
    cA
    cB
    cH
    wf1
    #
    @3
    @14
    @13
    cA
    cB
    cH
    wf
    #
    @18
    @19
    wceq
    #
    va
    vb
    weq
    #
    wi
    #
    vb
    cA
    wral
    va
    cA
    wral
    @22
    @13
    @3
    @23
    @2
    @3
    @11
    simprl
    #
    cA
    cB
    cH
    fof
    #
    syl
    @13
    @26
    va
    vb
    cA
    cA
    @13
    @15
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
    @25
    @24
    @32
    @25
    wn
    #
    @17
    @16
    @15
    cR
    wbr
    #
    wo
    #
    @24
    wn
    #
    @13
    @0
    @31
    @35
    @33
    wb
    @0
    @1
    @12
    simpll
    #
    @0
    @31
    wa
    #
    @25
    @35
    cA
    @15
    @16
    cR
    sotrieq
    con2bid
    sylan
    @32
    @17
    @36
    @34
    @32
    @17
    @20
    @36
    @13
    @11
    @31
    @17
    @20
    wi
    #
    @2
    @3
    @11
    simprr
    #
    @31
    @11
    @39
    @10
    @39
    @15
    @5
    cR
    wbr
    #
    @18
    @8
    cS
    wbr
    #
    wi
    vx
    vy
    @15
    @16
    cA
    cA
    vx
    va
    weq
    #
    @6
    @41
    @9
    @42
    @4
    @15
    @5
    cR
    breq1
    @43
    @7
    @18
    @8
    cS
    @4
    @15
    cH
    fveq2
    breq1d
    imbi12d
    vy
    vb
    weq
    #
    @41
    @17
    @42
    @20
    @5
    @16
    @15
    cR
    breq2
    @44
    @8
    @19
    @18
    cS
    @5
    @16
    cH
    fveq2
    breq2d
    imbi12d
    rspc2va
    ancoms
    sylan
    #
    @32
    @24
    @20
    @32
    @1
    @19
    cB
    wcel
    #
    @24
    @20
    wn
    #
    wi
    @0
    @1
    @12
    @31
    simpllr
    #
    @32
    cA
    cB
    @16
    cH
    @32
    @3
    @23
    @2
    @3
    @11
    @31
    simplrl
    @28
    syl
    #
    @13
    @29
    @30
    simprr
    ffvelrnd
    #
    @1
    @46
    wa
    #
    @47
    @24
    @19
    @19
    cS
    wbr
    #
    wn
    #
    cB
    @19
    cS
    poirr
    #
    @24
    @20
    @52
    @18
    @19
    @19
    cS
    breq1
    notbid
    syl5ibrcom
    syl2anc
    con2d
    syld
    @32
    @34
    @19
    @18
    cS
    wbr
    #
    @36
    @13
    @11
    @31
    @34
    @55
    wi
    #
    @40
    @11
    @30
    @29
    @56
    @30
    @29
    wa
    @11
    @56
    @10
    @56
    @16
    @5
    cR
    wbr
    #
    @19
    @8
    cS
    wbr
    #
    wi
    vx
    vy
    @16
    @15
    cA
    cA
    vx
    vb
    weq
    #
    @6
    @57
    @9
    @58
    @4
    @16
    @5
    cR
    breq1
    @59
    @7
    @19
    @8
    cS
    @4
    @16
    cH
    fveq2
    breq1d
    imbi12d
    vy
    va
    weq
    #
    @57
    @34
    @58
    @55
    @5
    @15
    @16
    cR
    breq2
    @60
    @8
    @18
    @19
    cS
    @5
    @15
    cH
    fveq2
    breq2d
    imbi12d
    rspc2va
    ancoms
    ancom2s
    sylan
    #
    @32
    @24
    @55
    @32
    @1
    @46
    @24
    @55
    wn
    #
    wi
    @48
    @50
    @51
    @62
    @24
    @53
    @54
    @24
    @55
    @52
    @18
    @19
    @19
    cS
    breq2
    notbid
    syl5ibrcom
    syl2anc
    con2d
    syld
    jaod
    sylbird
    con4d
    ralrimivva
    va
    vb
    cA
    cB
    cH
    dff13
    sylanbrc
    @27
    cA
    cB
    cH
    df-f1o
    sylanbrc
    @13
    @21
    va
    vb
    cA
    cA
    @32
    @17
    @20
    @45
    @32
    @17
    wn
    #
    @25
    @34
    wo
    #
    @47
    @13
    @0
    @31
    @64
    @63
    wb
    @37
    @38
    @17
    @64
    cA
    @15
    @16
    cR
    sotric
    con2bid
    sylan
    @32
    @25
    @47
    @34
    @32
    @1
    @46
    @25
    @47
    wi
    @48
    @50
    @51
    @47
    @25
    @53
    @54
    @25
    @20
    @52
    @25
    @18
    @19
    @19
    cS
    @15
    @16
    cH
    fveq2
    breq1d
    notbid
    syl5ibrcom
    syl2anc
    @32
    @34
    @55
    @47
    @61
    @32
    @1
    @46
    @18
    cB
    wcel
    #
    @55
    @47
    wi
    #
    @48
    @50
    @32
    cA
    cB
    @15
    cH
    @49
    @13
    @29
    @30
    simprl
    ffvelrnd
    @1
    @46
    @65
    wa
    wa
    @55
    @20
    wa
    wn
    @66
    cB
    @19
    @18
    cS
    po2nr
    @55
    @20
    imnan
    sylibr
    syl12anc
    syld
    jaod
    sylbird
    impcon4bid
    ralrimivva
    va
    vb
    cA
    cB
    cR
    cS
    cH
    df-isom
    sylanbrc
end
