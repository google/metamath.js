include "ctotbnd.mm"
include "cfv.mm"
include "wcel.mm"
include "cme.mm"
include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "cbl.mm"
include "co.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "cfn.mm"
include "crp.mm"
include "ciun.mm"
include "cpw.mm"
include "cin.mm"
include "istotbnd.mm"
include "wf.mm"
include "wex.mm"
include "wi.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "ac6sfi.mm"
include "ex.mm"
include "ad2antlr.mm"
include "crn.mm"
include "wss.mm"
include "simprrl.mm"
include "frn.mm"
include "syl.mm"
include "wfo.mm"
include "simplr.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn4.mm"
include "sylib.mm"
include "fofi.mm"
include "syl2anc.mm"
include "elfpw.mm"
include "sylanbrc.mm"
include "wb.mm"
include "eleq2d.mm"
include "rexrn.mm"
include "eliun.mm"
include "3bitr4g.mm"
include "eqrdv.mm"
include "simprrr.mm"
include "iuneq2.mm"
include "uniiun.mm"
include "simprl.mm"
include "syl5eqr.mm"
include "3eqtr2d.mm"
include "iuneq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "expr.mm"
include "exlimdv.mm"
include "syld.mm"
include "expimpd.mm"
include "rexlimdva.mm"
include "cmpt.mm"
include "cab.mm"
include "simprbi.mm"
include "ad2antrl.mm"
include "mptfi.mm"
include "rnfi.mm"
include "3syl.mm"
include "ovex.mm"
include "dfiun3.mm"
include "simprr.mm"
include "eqid.mm"
include "rnmpt.mm"
include "simplbi.mm"
include "ssrexv.mm"
include "ss2abdv.mm"
include "syl5eqss.mm"
include "unieq.mm"
include "ssabral.mm"
include "sseq1.mm"
include "syl5bbr.mm"
include "anbi12d.mm"
include "syl12anc.mm"
include "impbid.mm"
include "ralbidv.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem istotbnd3
  let vx: setvar x
  let vv: setvar v
  let cM: class M
  let cX: class X
  let vd: setvar d
  let vb: setvar b
  let vf: setvar f
  let vw: setvar w

  disjoint d v
  disjoint d x
  disjoint M d
  disjoint v x
  disjoint M v
  disjoint M x
  disjoint X d
  disjoint X v
  disjoint X x
  disjoint b d
  disjoint b f
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint M b
  disjoint d f
  disjoint d w
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint M f
  disjoint v w
  disjoint w x
  disjoint M w
  disjoint X b
  disjoint X f
  disjoint X w
  assert |- ( M e. ( TotBnd ` X ) <-> ( M e. ( Met ` X ) /\ A. d e. RR+ E. v e. ( ~P X i^i Fin ) U_ x e. v ( x ( ball ` M ) d ) = X ) )

  proof
    cM
    cX
    ctotbnd
    cfv
    wcel
    cM
    cX
    cme
    cfv
    wcel
    #
    vw
    cv
    #
    cuni
    #
    cX
    wceq
    #
    vb
    cv
    #
    vx
    cv
    #
    vd
    cv
    #
    cM
    cbl
    cfv
    #
    co
    #
    wceq
    #
    vx
    cX
    wrex
    #
    vb
    @1
    wral
    #
    wa
    #
    vw
    cfn
    wrex
    #
    vd
    crp
    wral
    #
    wa
    @0
    vx
    vv
    cv
    #
    @8
    ciun
    #
    cX
    wceq
    #
    vv
    cX
    cpw
    cfn
    cin
    #
    wrex
    #
    vd
    crp
    wral
    #
    wa
    vx
    vw
    cM
    cX
    vb
    vd
    istotbnd
    @0
    @14
    @20
    @0
    @13
    @19
    vd
    crp
    @0
    @13
    @19
    @0
    @12
    @19
    vw
    cfn
    @0
    @1
    cfn
    wcel
    #
    wa
    #
    @3
    @11
    @19
    @22
    @3
    wa
    #
    @11
    @1
    cX
    vf
    cv
    #
    wf
    #
    @4
    @4
    @24
    cfv
    #
    @6
    @7
    co
    #
    wceq
    #
    vb
    @1
    wral
    #
    wa
    #
    vf
    wex
    #
    @19
    @21
    @11
    @31
    wi
    @0
    @3
    @21
    @11
    @31
    @9
    @28
    vb
    vx
    @1
    cX
    vf
    @5
    @26
    wceq
    #
    @8
    @27
    @4
    @5
    @26
    @6
    @7
    oveq1
    #
    eqeq2d
    ac6sfi
    ex
    ad2antlr
    @23
    @30
    @19
    vf
    @22
    @3
    @30
    @19
    @22
    @3
    @30
    wa
    #
    wa
    #
    @24
    crn
    #
    @18
    wcel
    #
    vx
    @36
    @8
    ciun
    #
    cX
    wceq
    #
    @19
    @35
    @36
    cX
    wss
    #
    @36
    cfn
    wcel
    #
    @37
    @35
    @25
    @40
    @22
    @3
    @25
    @29
    simprrl
    #
    @1
    cX
    @24
    frn
    syl
    @35
    @21
    @1
    @36
    @24
    wfo
    #
    @41
    @0
    @21
    @34
    simplr
    @35
    @24
    @1
    wfn
    #
    @43
    @35
    @25
    @44
    @42
    @1
    cX
    @24
    ffn
    syl
    #
    @1
    @24
    dffn4
    sylib
    @1
    @36
    @24
    fofi
    syl2anc
    @36
    cX
    elfpw
    sylanbrc
    @35
    @38
    vb
    @1
    @27
    ciun
    #
    vb
    @1
    @4
    ciun
    #
    cX
    @35
    vv
    @38
    @46
    @35
    @15
    @8
    wcel
    #
    vx
    @36
    wrex
    #
    @15
    @27
    wcel
    #
    vb
    @1
    wrex
    #
    @15
    @38
    wcel
    @15
    @46
    wcel
    @35
    @44
    @49
    @51
    wb
    @45
    @48
    @50
    vx
    vb
    @1
    @24
    @32
    @8
    @27
    @15
    @33
    eleq2d
    rexrn
    syl
    vx
    @15
    @36
    @8
    eliun
    vb
    @15
    @1
    @27
    eliun
    3bitr4g
    eqrdv
    @35
    @29
    @47
    @46
    wceq
    @22
    @3
    @25
    @29
    simprrr
    vb
    @1
    @4
    @27
    iuneq2
    syl
    @35
    @47
    @2
    cX
    vb
    @1
    uniiun
    @22
    @3
    @30
    simprl
    syl5eqr
    3eqtr2d
    @17
    @39
    vv
    @36
    @18
    @15
    @36
    wceq
    @16
    @38
    cX
    vx
    @15
    @36
    @8
    iuneq1
    eqeq1d
    rspcev
    syl2anc
    expr
    exlimdv
    syld
    expimpd
    rexlimdva
    @0
    @17
    @13
    vv
    @18
    @0
    @15
    @18
    wcel
    #
    @17
    @13
    @0
    @52
    @17
    wa
    wa
    #
    vx
    @15
    @8
    cmpt
    #
    crn
    #
    cfn
    wcel
    #
    @55
    cuni
    #
    cX
    wceq
    #
    @55
    @10
    vb
    cab
    #
    wss
    #
    @13
    @53
    @15
    cfn
    wcel
    #
    @54
    cfn
    wcel
    @56
    @52
    @61
    @0
    @17
    @52
    @15
    cX
    wss
    #
    @61
    @15
    cX
    elfpw
    #
    simprbi
    ad2antrl
    vx
    @15
    @8
    mptfi
    @54
    rnfi
    3syl
    @53
    @57
    @16
    cX
    vx
    @15
    @8
    @5
    @6
    @7
    ovex
    dfiun3
    @0
    @52
    @17
    simprr
    syl5eqr
    @53
    @55
    @9
    vx
    @15
    wrex
    #
    vb
    cab
    @59
    vx
    vb
    @15
    @8
    @54
    @54
    eqid
    rnmpt
    @53
    @64
    @10
    vb
    @53
    @62
    @64
    @10
    wi
    @52
    @62
    @0
    @17
    @52
    @62
    @61
    @63
    simplbi
    ad2antrl
    @9
    vx
    @15
    cX
    ssrexv
    syl
    ss2abdv
    syl5eqss
    @12
    @58
    @60
    wa
    vw
    @55
    cfn
    @1
    @55
    wceq
    #
    @3
    @58
    @11
    @60
    @65
    @2
    @57
    cX
    @1
    @55
    unieq
    eqeq1d
    @11
    @1
    @59
    wss
    @65
    @60
    @10
    vb
    @1
    ssabral
    @1
    @55
    @59
    sseq1
    syl5bbr
    anbi12d
    rspcev
    syl12anc
    expr
    rexlimdva
    impbid
    ralbidv
    pm5.32i
    bitri
end
