include "crn.mm"
include "wcel.mm"
include "cmex.mm"
include "cfv.mm"
include "cv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "cmpt.mm"
include "wceq.mm"
include "cmrsub.mm"
include "wrex.mm"
include "ccom.mm"
include "eqid.mm"
include "elmsubrn.mm"
include "eleq2i.mm"
include "fvex.mm"
include "mptex.mm"
include "elrnmpti.mm"
include "bitri.mm"
include "wa.mm"
include "reeanv.mm"
include "cmtc.mm"
include "cmrex.mm"
include "cxp.mm"
include "simpr.mm"
include "mexval.mm"
include "syl6eleq.mm"
include "xp1st.mm"
include "syl.mm"
include "wf.mm"
include "mrsubf.mm"
include "ad2antlr.mm"
include "xp2nd.mm"
include "ffvelrnd.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "syl6eleqr.mm"
include "eqidd.mm"
include "op1std.mm"
include "op2ndd.mm"
include "fveq2d.mm"
include "opeq12d.mm"
include "fmptco.mm"
include "fvco3.mm"
include "opeq2d.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"
include "cvv.mm"
include "mrsubco.mm"
include "fveq1.mm"
include "mpteq2dv.mm"
include "elrnmpt1s.mm"
include "sylancl.mm"
include "eqeltrd.mm"
include "coeq1.mm"
include "coeq2.mm"
include "sylan9eq.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "rexlimivv.mm"
include "sylbir.mm"
include "syl2anb.mm"

theorem msubco
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  assume msubco.s: |- S = ( mSubst ` T )


  assert |- ( ( F e. ran S /\ G e. ran S ) -> ( F o. G ) e. ran S )

  proof
    cF
    cS
    crn
    #
    wcel
    #
    cF
    vx
    cT
    cmex
    cfv
    #
    vx
    cv
    #
    c1st
    cfv
    #
    @3
    c2nd
    cfv
    #
    vf
    cv
    #
    cfv
    #
    cop
    #
    cmpt
    #
    wceq
    #
    vf
    cT
    cmrsub
    cfv
    #
    crn
    #
    wrex
    #
    cG
    vy
    @2
    vy
    cv
    #
    c1st
    cfv
    #
    @14
    c2nd
    cfv
    #
    vg
    cv
    #
    cfv
    #
    cop
    #
    cmpt
    #
    wceq
    #
    vg
    @12
    wrex
    #
    cF
    cG
    ccom
    #
    @0
    wcel
    #
    cG
    @0
    wcel
    #
    @1
    cF
    vf
    @12
    @9
    cmpt
    #
    crn
    #
    wcel
    @13
    @0
    @27
    cF
    cS
    cT
    vx
    vf
    @2
    @11
    @2
    eqid
    #
    @11
    eqid
    #
    msubco.s
    elmsubrn
    eleq2i
    vf
    @12
    @9
    cF
    @26
    @26
    eqid
    vx
    @2
    @8
    cT
    cmex
    fvex
    #
    mptex
    elrnmpti
    bitri
    @25
    cG
    vg
    @12
    @20
    cmpt
    #
    crn
    #
    wcel
    @22
    @0
    @32
    cG
    cS
    cT
    vy
    vg
    @2
    @11
    @28
    @29
    msubco.s
    elmsubrn
    eleq2i
    vg
    @12
    @20
    cG
    @31
    @31
    eqid
    vy
    @2
    @19
    @30
    mptex
    elrnmpti
    bitri
    @13
    @22
    wa
    @10
    @21
    wa
    #
    vg
    @12
    wrex
    vf
    @12
    wrex
    @24
    @10
    @21
    vf
    vg
    @12
    @12
    reeanv
    @33
    @24
    vf
    vg
    @12
    @12
    @6
    @12
    wcel
    #
    @17
    @12
    wcel
    #
    wa
    #
    @24
    @33
    @9
    @20
    ccom
    #
    @0
    wcel
    @36
    @37
    vy
    @2
    @15
    @16
    @6
    @17
    ccom
    #
    cfv
    #
    cop
    #
    cmpt
    #
    @0
    @36
    @37
    vy
    @2
    @15
    @18
    @6
    cfv
    #
    cop
    #
    cmpt
    @41
    @36
    vy
    vx
    @2
    @2
    @19
    @8
    @43
    @20
    @9
    @36
    @14
    @2
    wcel
    #
    wa
    #
    @19
    cT
    cmtc
    cfv
    #
    cT
    cmrex
    cfv
    #
    cxp
    #
    @2
    @45
    @15
    @46
    wcel
    #
    @18
    @47
    wcel
    @19
    @48
    wcel
    @45
    @14
    @48
    wcel
    #
    @49
    @45
    @14
    @2
    @48
    @36
    @44
    simpr
    @47
    cT
    @2
    @46
    @46
    eqid
    @28
    @47
    eqid
    #
    mexval
    #
    syl6eleq
    #
    @14
    @46
    @47
    xp1st
    syl
    @45
    @47
    @47
    @16
    @17
    @35
    @47
    @47
    @17
    wf
    #
    @34
    @44
    @47
    @11
    cT
    @17
    @29
    @51
    mrsubf
    ad2antlr
    #
    @45
    @50
    @16
    @47
    wcel
    #
    @53
    @14
    @46
    @47
    xp2nd
    syl
    #
    ffvelrnd
    @15
    @18
    @46
    @47
    opelxpi
    syl2anc
    @52
    syl6eleqr
    @36
    @20
    eqidd
    @36
    @9
    eqidd
    @3
    @19
    wceq
    #
    @4
    @15
    @7
    @42
    @15
    @18
    @3
    @14
    c1st
    fvex
    #
    @16
    @17
    fvex
    #
    op1std
    @58
    @5
    @18
    @6
    @15
    @18
    @3
    @59
    @60
    op2ndd
    fveq2d
    opeq12d
    fmptco
    @36
    vy
    @2
    @40
    @43
    @45
    @39
    @42
    @15
    @45
    @54
    @56
    @39
    @42
    wceq
    @55
    @57
    @47
    @47
    @16
    @6
    @17
    fvco3
    syl2anc
    opeq2d
    mpteq2dva
    eqtr4d
    @36
    @41
    vh
    @12
    vy
    @2
    @15
    @16
    vh
    cv
    #
    cfv
    #
    cop
    #
    cmpt
    #
    cmpt
    #
    crn
    #
    @0
    @36
    @38
    @12
    wcel
    @41
    cvv
    wcel
    @41
    @66
    wcel
    @11
    cT
    @6
    @17
    @29
    mrsubco
    vy
    @2
    @40
    @30
    mptex
    vh
    @12
    @64
    @41
    @38
    @65
    cvv
    @65
    eqid
    @61
    @38
    wceq
    #
    vy
    @2
    @63
    @40
    @67
    @62
    @39
    @15
    @16
    @61
    @38
    fveq1
    opeq2d
    mpteq2dv
    elrnmpt1s
    sylancl
    cS
    cT
    vy
    vh
    @2
    @11
    @28
    @29
    msubco.s
    elmsubrn
    syl6eleqr
    eqeltrd
    @33
    @23
    @37
    @0
    @10
    @21
    @23
    @9
    cG
    ccom
    @37
    cF
    @9
    cG
    coeq1
    cG
    @20
    @9
    coeq2
    sylan9eq
    eleq1d
    syl5ibrcom
    rexlimivv
    sylbir
    syl2anb
end
