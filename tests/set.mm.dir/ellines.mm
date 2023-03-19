include "clines2.mm"
include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "wne.mm"
include "cline2.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cee.mm"
include "cfv.mm"
include "wrex.mm"
include "cn.mm"
include "elex.mm"
include "wi.mm"
include "ovex.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "adantl.mm"
include "rexlimivw.mm"
include "a1i.mm"
include "rexlimivv.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "2rexbidv.mm"
include "w3a.mm"
include "cop.mm"
include "ccolin.mm"
include "ccnv.mm"
include "cec.mm"
include "wex.mm"
include "cab.mm"
include "crn.mm"
include "coprab.mm"
include "df-lines2.mm"
include "df-line2.mm"
include "rneqi.mm"
include "rnoprab.mm"
include "3eqtri.mm"
include "eleq2i.mm"
include "abid.mm"
include "df-rex.mm"
include "2exbii.mm"
include "exrot3.mm"
include "r2ex.mm"
include "r19.42v.mm"
include "bitr3i.mm"
include "bitri.mm"
include "anass.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simpll.mm"
include "simpr.mm"
include "3jca.mm"
include "jca.mm"
include "simpr2.mm"
include "simpl.mm"
include "simpr1.mm"
include "jca32.mm"
include "simpr3.mm"
include "impbii.mm"
include "anbi1i.mm"
include "wbr.mm"
include "fvline.mm"
include "opex.mm"
include "dfec2.mm"
include "ax-mp.mm"
include "vex.mm"
include "brcnv.mm"
include "abbii.mm"
include "eqtri.mm"
include "syl6eqr.mm"
include "eqeq2d.mm"
include "pm5.32i.mm"
include "3bitrri.mm"
include "3exbii.mm"
include "3bitr4ri.mm"
include "vtoclbg.mm"
include "pm5.21nii.mm"

theorem ellines
  let cA: class A
  let vn: setvar n
  let vq: setvar q
  let vp: setvar p
  let vx: setvar x

  disjoint A n
  disjoint A p
  disjoint A q
  disjoint n p
  disjoint n q
  disjoint p q
  disjoint A x
  disjoint n x
  disjoint p x
  disjoint q x
  assert |- ( A e. LinesEE <-> E. n e. NN E. p e. ( EE ` n ) E. q e. ( EE ` n ) ( p =/= q /\ A = ( p Line q ) ) )

  proof
    cA
    clines2
    wcel
    #
    cA
    cvv
    wcel
    #
    vp
    cv
    #
    vq
    cv
    #
    wne
    #
    cA
    @2
    @3
    cline2
    co
    #
    wceq
    #
    wa
    #
    vq
    vn
    cv
    #
    cee
    cfv
    #
    wrex
    #
    vp
    @9
    wrex
    vn
    cn
    wrex
    #
    cA
    clines2
    elex
    @10
    @1
    vn
    vp
    cn
    @9
    @10
    @1
    wi
    @8
    cn
    wcel
    #
    @2
    @9
    wcel
    #
    wa
    #
    @7
    @1
    vq
    @9
    @6
    @1
    @4
    @6
    @1
    @5
    cvv
    wcel
    @2
    @3
    cline2
    ovex
    cA
    @5
    cvv
    eleq1
    mpbiri
    adantl
    rexlimivw
    a1i
    rexlimivv
    vx
    cv
    #
    clines2
    wcel
    #
    @4
    @15
    @5
    wceq
    #
    wa
    #
    vq
    @9
    wrex
    #
    vp
    @9
    wrex
    vn
    cn
    wrex
    #
    @0
    @11
    vx
    cA
    cvv
    @15
    cA
    clines2
    eleq1
    @15
    cA
    wceq
    #
    @19
    @10
    vn
    vp
    cn
    @9
    @21
    @18
    @7
    vq
    @9
    @21
    @17
    @6
    @4
    @15
    cA
    @5
    eqeq1
    anbi2d
    rexbidv
    2rexbidv
    @16
    @15
    @13
    @3
    @9
    wcel
    #
    @4
    w3a
    #
    @15
    @2
    @3
    cop
    #
    ccolin
    ccnv
    #
    cec
    #
    wceq
    #
    wa
    #
    vn
    cn
    wrex
    #
    vq
    wex
    vp
    wex
    #
    vx
    cab
    #
    wcel
    #
    @20
    clines2
    @31
    @15
    clines2
    cline2
    crn
    @29
    vp
    vq
    vx
    coprab
    #
    crn
    @31
    df-lines2
    cline2
    @33
    vn
    vp
    vq
    vx
    df-line2
    rneqi
    @29
    vp
    vq
    vx
    rnoprab
    3eqtri
    eleq2i
    @32
    @30
    @20
    @30
    vx
    abid
    @30
    @12
    @28
    wa
    #
    vn
    wex
    #
    vq
    wex
    vp
    wex
    #
    @20
    @29
    @35
    vp
    vq
    @28
    vn
    cn
    df-rex
    2exbii
    @22
    @14
    @18
    wa
    #
    wa
    #
    vq
    wex
    #
    vp
    wex
    vn
    wex
    #
    @38
    vn
    wex
    vq
    wex
    vp
    wex
    @20
    @36
    @38
    vn
    vp
    vq
    exrot3
    @20
    @14
    @19
    wa
    #
    vp
    wex
    vn
    wex
    @40
    @19
    vn
    vp
    cn
    @9
    r2ex
    @41
    @39
    vn
    vp
    @41
    @37
    vq
    @9
    wrex
    @39
    @14
    @18
    vq
    @9
    r19.42v
    @37
    vq
    @9
    df-rex
    bitr3i
    2exbii
    bitri
    @34
    @38
    vp
    vq
    vn
    @38
    @12
    @23
    wa
    #
    @17
    wa
    #
    @42
    @27
    wa
    @34
    @38
    @22
    @14
    wa
    #
    @18
    wa
    #
    @43
    @22
    @14
    @18
    anass
    @45
    @44
    @4
    wa
    #
    @17
    wa
    @43
    @44
    @4
    @17
    anass
    @46
    @42
    @17
    @46
    @42
    @46
    @12
    @23
    @22
    @12
    @13
    @4
    simplrl
    @46
    @13
    @22
    @4
    @22
    @12
    @13
    @4
    simplrr
    @22
    @14
    @4
    simpll
    @44
    @4
    simpr
    3jca
    jca
    @42
    @44
    @4
    @42
    @22
    @12
    @13
    @12
    @13
    @22
    @4
    simpr2
    @12
    @23
    simpl
    @12
    @13
    @22
    @4
    simpr1
    jca32
    @12
    @13
    @22
    @4
    simpr3
    jca
    impbii
    anbi1i
    bitr3i
    bitr3i
    @42
    @17
    @27
    @42
    @5
    @26
    @15
    @42
    @5
    @15
    @24
    ccolin
    wbr
    #
    vx
    cab
    #
    @26
    vx
    @2
    @3
    @8
    fvline
    @26
    @24
    @15
    @25
    wbr
    #
    vx
    cab
    #
    @48
    @24
    cvv
    wcel
    @26
    @50
    wceq
    @2
    @3
    opex
    #
    vx
    @24
    @25
    cvv
    dfec2
    ax-mp
    @49
    @47
    vx
    @24
    @15
    ccolin
    @51
    vx
    vex
    brcnv
    abbii
    eqtri
    syl6eqr
    eqeq2d
    pm5.32i
    @12
    @23
    @27
    anass
    3bitrri
    3exbii
    3bitr4ri
    bitri
    bitri
    bitri
    vtoclbg
    pm5.21nii
end
