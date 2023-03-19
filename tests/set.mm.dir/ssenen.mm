include "cen.mm"
include "wbr.mm"
include "cpw.mm"
include "cv.mm"
include "cab.mm"
include "cin.mm"
include "wss.mm"
include "wa.mm"
include "wf1o.mm"
include "wex.mm"
include "bren.mm"
include "cima.mm"
include "ccnv.mm"
include "cvv.mm"
include "wcel.mm"
include "cdm.mm"
include "f1odm.mm"
include "vex.mm"
include "dmex.mm"
include "syl6eqelr.mm"
include "pwexg.mm"
include "inex1g.mm"
include "3syl.mm"
include "crn.mm"
include "wfo.mm"
include "wceq.mm"
include "f1ofo.mm"
include "forn.mm"
include "syl.mm"
include "rnex.mm"
include "wf1.mm"
include "f1of1.mm"
include "adantr.mm"
include "simpr.mm"
include "a1i.mm"
include "f1imaen2g.mm"
include "syl22anc.mm"
include "entr.mm"
include "sylan.mm"
include "expl.mm"
include "imassrn.mm"
include "syl5sseq.mm"
include "jctild.mm"
include "elin.mm"
include "elpw.mm"
include "breq1.mm"
include "elab.mm"
include "anbi12i.mm"
include "bitri.mm"
include "imaex.mm"
include "3imtr4g.mm"
include "wi.mm"
include "f1ocnv.mm"
include "f1f1orn.mm"
include "f1imaen.mm"
include "cnvex.mm"
include "wb.mm"
include "simpl.mm"
include "elpwid.mm"
include "sylbi.mm"
include "imaeq2.mm"
include "wrel.mm"
include "f1orel.mm"
include "dfrel2.mm"
include "sylib.mm"
include "imaeq1d.mm"
include "f1imacnv.mm"
include "eqtr3d.mm"
include "sylan9eqr.mm"
include "eqcomd.mm"
include "ex.mm"
include "sylan2.mm"
include "adantrl.mm"
include "adantrr.mm"
include "impbid.mm"
include "en3d.mm"
include "exlimiv.mm"
include "df-pw.mm"
include "ineq1i.mm"
include "inab.mm"
include "eqtri.mm"
include "3brtr3g.mm"

theorem ssenen
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint x y
  disjoint x z
  disjoint f x
  disjoint y z
  disjoint f y
  disjoint A y
  disjoint f z
  disjoint A z
  disjoint A f
  disjoint B y
  disjoint B z
  disjoint B f
  disjoint C y
  disjoint C z
  disjoint C f
  assert |- ( A ~~ B -> { x | ( x C_ A /\ x ~~ C ) } ~~ { x | ( x C_ B /\ x ~~ C ) } )

  proof
    cA
    cB
    cen
    wbr
    #
    cA
    cpw
    #
    vx
    cv
    #
    cC
    cen
    wbr
    #
    vx
    cab
    #
    cin
    #
    cB
    cpw
    #
    @4
    cin
    #
    @2
    cA
    wss
    #
    @3
    wa
    vx
    cab
    #
    @2
    cB
    wss
    #
    @3
    wa
    vx
    cab
    #
    cen
    @0
    cA
    cB
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    @5
    @7
    cen
    wbr
    #
    cA
    cB
    vf
    bren
    @13
    @14
    vf
    @13
    vy
    vz
    @5
    @7
    @12
    vy
    cv
    #
    cima
    #
    @12
    ccnv
    #
    vz
    cv
    #
    cima
    #
    @13
    cA
    cvv
    wcel
    @1
    cvv
    wcel
    @5
    cvv
    wcel
    @13
    cA
    @12
    cdm
    cvv
    cA
    cB
    @12
    f1odm
    @12
    vf
    vex
    #
    dmex
    syl6eqelr
    cA
    cvv
    pwexg
    @1
    @4
    cvv
    inex1g
    3syl
    @13
    cB
    cvv
    wcel
    #
    @6
    cvv
    wcel
    @7
    cvv
    wcel
    @13
    cB
    @12
    crn
    #
    cvv
    @13
    cA
    cB
    @12
    wfo
    #
    @22
    cB
    wceq
    cA
    cB
    @12
    f1ofo
    #
    cA
    cB
    @12
    forn
    #
    syl
    @12
    @20
    rnex
    syl6eqelr
    #
    cB
    cvv
    pwexg
    @6
    @4
    cvv
    inex1g
    3syl
    @13
    @15
    cA
    wss
    #
    @15
    cC
    cen
    wbr
    #
    wa
    #
    @16
    cB
    wss
    #
    @16
    cC
    cen
    wbr
    #
    wa
    #
    @15
    @5
    wcel
    #
    @16
    @7
    wcel
    #
    @13
    @29
    @31
    @30
    @13
    @27
    @28
    @31
    @13
    @27
    wa
    #
    @16
    @15
    cen
    wbr
    #
    @28
    @31
    @35
    cA
    cB
    @12
    wf1
    #
    @21
    @27
    @15
    cvv
    wcel
    #
    @36
    @13
    @37
    @27
    cA
    cB
    @12
    f1of1
    #
    adantr
    @13
    @21
    @27
    @26
    adantr
    @13
    @27
    simpr
    @38
    @35
    vy
    vex
    #
    a1i
    cA
    cB
    @15
    @12
    cvv
    f1imaen2g
    syl22anc
    @16
    @15
    cC
    entr
    sylan
    expl
    @13
    @23
    @30
    @24
    @23
    @22
    @16
    cB
    @12
    @15
    imassrn
    @25
    syl5sseq
    syl
    jctild
    @33
    @15
    @1
    wcel
    #
    @15
    @4
    wcel
    #
    wa
    #
    @29
    @15
    @1
    @4
    elin
    #
    @41
    @27
    @42
    @28
    @15
    cA
    @40
    elpw
    @3
    @28
    vx
    @15
    @40
    @2
    @15
    cC
    cen
    breq1
    elab
    anbi12i
    bitri
    @34
    @16
    @6
    wcel
    #
    @16
    @4
    wcel
    #
    wa
    @32
    @16
    @6
    @4
    elin
    @45
    @30
    @46
    @31
    @16
    cB
    @12
    @15
    @20
    imaex
    #
    elpw
    @3
    @31
    vx
    @16
    @47
    @2
    @16
    cC
    cen
    breq1
    elab
    anbi12i
    bitri
    3imtr4g
    @13
    @18
    cB
    wss
    #
    @18
    cC
    cen
    wbr
    #
    wa
    #
    @19
    cA
    wss
    #
    @19
    cC
    cen
    wbr
    #
    wa
    #
    @18
    @7
    wcel
    #
    @19
    @5
    wcel
    #
    @13
    cB
    cA
    @17
    wf1o
    #
    @50
    @53
    wi
    cA
    cB
    @12
    f1ocnv
    #
    @56
    @50
    @52
    @51
    @56
    @48
    @49
    @52
    @56
    @48
    wa
    @19
    @18
    cen
    wbr
    #
    @49
    @52
    @56
    cB
    @17
    crn
    #
    @17
    wf1
    #
    @48
    @58
    @56
    cB
    cA
    @17
    wf1
    #
    cB
    @59
    @17
    wf1o
    @60
    cB
    cA
    @17
    f1of1
    #
    cB
    cA
    @17
    f1f1orn
    cB
    @59
    @17
    f1of1
    3syl
    cB
    @59
    @18
    @17
    vz
    vex
    #
    f1imaen
    sylan
    @19
    @18
    cC
    entr
    sylan
    expl
    @56
    cB
    cA
    @17
    wfo
    #
    @51
    cB
    cA
    @17
    f1ofo
    @64
    @59
    @19
    cA
    @17
    @18
    imassrn
    cB
    cA
    @17
    forn
    syl5sseq
    syl
    jctild
    syl
    @54
    @18
    @6
    wcel
    #
    @18
    @4
    wcel
    #
    wa
    #
    @50
    @18
    @6
    @4
    elin
    #
    @65
    @48
    @66
    @49
    @18
    cB
    @63
    elpw
    @3
    @49
    vx
    @18
    @63
    @2
    @18
    cC
    cen
    breq1
    elab
    anbi12i
    bitri
    @55
    @19
    @1
    wcel
    #
    @19
    @4
    wcel
    #
    wa
    @53
    @19
    @1
    @4
    elin
    @69
    @51
    @70
    @52
    @19
    cA
    @17
    @18
    @12
    @20
    cnvex
    imaex
    #
    elpw
    @3
    @52
    vx
    @19
    @71
    @2
    @19
    cC
    cen
    breq1
    elab
    anbi12i
    bitri
    3imtr4g
    @13
    @33
    @54
    wa
    #
    @15
    @19
    wceq
    #
    @18
    @16
    wceq
    #
    wb
    @13
    @72
    wa
    @73
    @74
    @13
    @54
    @73
    @74
    wi
    #
    @33
    @54
    @13
    @48
    @75
    @54
    @67
    @48
    @68
    @67
    @18
    cB
    @65
    @66
    simpl
    elpwid
    sylbi
    @13
    @48
    wa
    #
    @73
    @74
    @76
    @73
    wa
    @16
    @18
    @73
    @76
    @16
    @12
    @19
    cima
    #
    @18
    @15
    @19
    @12
    imaeq2
    @76
    @17
    ccnv
    #
    @19
    cima
    #
    @77
    @18
    @13
    @79
    @77
    wceq
    @48
    @13
    @78
    @12
    @19
    @13
    @12
    wrel
    @78
    @12
    wceq
    cA
    cB
    @12
    f1orel
    @12
    dfrel2
    sylib
    imaeq1d
    adantr
    @13
    @61
    @48
    @79
    @18
    wceq
    @13
    @56
    @61
    @57
    @62
    syl
    cB
    cA
    @18
    @17
    f1imacnv
    sylan
    eqtr3d
    sylan9eqr
    eqcomd
    ex
    sylan2
    adantrl
    @13
    @33
    @74
    @73
    wi
    #
    @54
    @33
    @13
    @27
    @80
    @33
    @43
    @27
    @44
    @43
    @15
    cA
    @41
    @42
    simpl
    elpwid
    sylbi
    @35
    @74
    @73
    @35
    @74
    wa
    @19
    @15
    @74
    @35
    @19
    @17
    @16
    cima
    #
    @15
    @18
    @16
    @17
    imaeq2
    @13
    @37
    @27
    @81
    @15
    wceq
    @39
    cA
    cB
    @15
    @12
    f1imacnv
    sylan
    sylan9eqr
    eqcomd
    ex
    sylan2
    adantrr
    impbid
    ex
    en3d
    exlimiv
    sylbi
    @5
    @8
    vx
    cab
    #
    @4
    cin
    @9
    @1
    @82
    @4
    vx
    cA
    df-pw
    ineq1i
    @8
    @3
    vx
    inab
    eqtri
    @7
    @10
    vx
    cab
    #
    @4
    cin
    @11
    @6
    @83
    @4
    vx
    cB
    df-pw
    ineq1i
    @10
    @3
    vx
    inab
    eqtri
    3brtr3g
end
