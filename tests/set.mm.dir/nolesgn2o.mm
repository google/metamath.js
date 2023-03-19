include "csur.mm"
include "wcel.mm"
include "con0.mm"
include "w3a.mm"
include "cres.mm"
include "wceq.mm"
include "cfv.mm"
include "c2o.mm"
include "wa.mm"
include "cslt.mm"
include "wbr.mm"
include "wn.mm"
include "c0.mm"
include "c1o.mm"
include "wo.mm"
include "w3o.mm"
include "simpl2.mm"
include "nofv.mm"
include "syl.mm"
include "3orel3.mm"
include "syl5com.mm"
include "cv.mm"
include "wral.mm"
include "cop.mm"
include "ctp.mm"
include "wrex.mm"
include "simp13.mm"
include "fveq1.mm"
include "eqcomd.mm"
include "adantr.mm"
include "simpr.mm"
include "fvresd.mm"
include "3eqtr3d.mm"
include "ralrimiva.mm"
include "3ad2ant2.mm"
include "simprr.mm"
include "a1d.mm"
include "ancld.mm"
include "orim12d.mm"
include "3impia.mm"
include "3mix3.mm"
include "3mix2.mm"
include "jaoi.mm"
include "fvex.mm"
include "brtp.mm"
include "sylibr.mm"
include "raleq.mm"
include "fveq2.mm"
include "breq12d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "wb.mm"
include "simp12.mm"
include "simp11.mm"
include "sltval.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "3expia.mm"
include "syld.mm"
include "con1d.mm"

theorem nolesgn2o
  let cA: class A
  let cB: class B
  let cX: class X
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( A e. No /\ B e. No /\ X e. On ) /\ ( ( A |` X ) = ( B |` X ) /\ ( A ` X ) = 2o ) /\ -. B <s A ) -> ( B ` X ) = 2o )

  proof
    cA
    csur
    wcel
    #
    cB
    csur
    wcel
    #
    cX
    con0
    wcel
    #
    w3a
    #
    cA
    cX
    cres
    #
    cB
    cX
    cres
    #
    wceq
    #
    cX
    cA
    cfv
    #
    c2o
    wceq
    #
    wa
    #
    cB
    cA
    cslt
    wbr
    #
    wn
    cX
    cB
    cfv
    #
    c2o
    wceq
    #
    @3
    @9
    wa
    #
    @12
    @10
    @13
    @12
    wn
    #
    @11
    c0
    wceq
    #
    @11
    c1o
    wceq
    #
    wo
    #
    @10
    @13
    @15
    @16
    @12
    w3o
    #
    @14
    @17
    @13
    @1
    @18
    @0
    @1
    @2
    @9
    simpl2
    cB
    cX
    nofv
    syl
    @15
    @16
    @12
    3orel3
    syl5com
    @3
    @9
    @17
    @10
    @3
    @9
    @17
    w3a
    #
    @10
    vy
    cv
    #
    cB
    cfv
    #
    @20
    cA
    cfv
    #
    wceq
    #
    vy
    vx
    cv
    #
    wral
    #
    @24
    cB
    cfv
    #
    @24
    cA
    cfv
    #
    c1o
    c0
    cop
    c1o
    c2o
    cop
    c0
    c2o
    cop
    ctp
    #
    wbr
    #
    wa
    #
    vx
    con0
    wrex
    #
    @19
    @2
    @23
    vy
    cX
    wral
    #
    @11
    @7
    @28
    wbr
    #
    @31
    @0
    @1
    @2
    @9
    @17
    simp13
    @9
    @3
    @32
    @17
    @6
    @32
    @8
    @6
    @23
    vy
    cX
    @6
    @20
    cX
    wcel
    #
    wa
    #
    @20
    @5
    cfv
    #
    @20
    @4
    cfv
    #
    @21
    @22
    @6
    @36
    @37
    wceq
    @34
    @6
    @37
    @36
    @20
    @4
    @5
    fveq1
    eqcomd
    adantr
    @35
    @20
    cX
    cB
    @6
    @34
    simpr
    #
    fvresd
    @35
    @20
    cX
    cA
    @38
    fvresd
    3eqtr3d
    ralrimiva
    adantr
    3ad2ant2
    @19
    @16
    @7
    c0
    wceq
    wa
    #
    @16
    @8
    wa
    #
    @15
    @8
    wa
    #
    w3o
    #
    @33
    @19
    @41
    @40
    wo
    #
    @42
    @3
    @9
    @17
    @43
    @13
    @15
    @41
    @16
    @40
    @13
    @15
    @8
    @13
    @8
    @15
    @3
    @6
    @8
    simprr
    #
    a1d
    ancld
    @13
    @16
    @8
    @13
    @8
    @16
    @44
    a1d
    ancld
    orim12d
    3impia
    @41
    @42
    @40
    @41
    @39
    @40
    3mix3
    @40
    @39
    @41
    3mix2
    jaoi
    syl
    c1o
    c0
    c1o
    c2o
    c0
    c2o
    @11
    @7
    cX
    cB
    fvex
    cX
    cA
    fvex
    brtp
    sylibr
    @30
    @32
    @33
    wa
    vx
    cX
    con0
    @24
    cX
    wceq
    #
    @25
    @32
    @29
    @33
    @23
    vy
    @24
    cX
    raleq
    @45
    @26
    @11
    @27
    @7
    @28
    @24
    cX
    cB
    fveq2
    @24
    cX
    cA
    fveq2
    breq12d
    anbi12d
    rspcev
    syl12anc
    @19
    @1
    @0
    @10
    @31
    wb
    @0
    @1
    @2
    @9
    @17
    simp12
    @0
    @1
    @2
    @9
    @17
    simp11
    vx
    vy
    cB
    cA
    sltval
    syl2anc
    mpbird
    3expia
    syld
    con1d
    3impia
end
