include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "cpnf.mm"
include "wceq.mm"
include "cmnf.mm"
include "w3o.mm"
include "cioo.mm"
include "co.mm"
include "cvol.mm"
include "cdm.mm"
include "elxr.mm"
include "wss.mm"
include "cv.mm"
include "covol.mm"
include "cfv.mm"
include "cin.mm"
include "cdif.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "ioossre.mm"
include "a1i.mm"
include "elpwi.mm"
include "wa.mm"
include "crp.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "cabs.mm"
include "cmin.mm"
include "c1.mm"
include "cseq.mm"
include "clt.mm"
include "csup.mm"
include "cxp.mm"
include "cn.mm"
include "cmap.mm"
include "wrex.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simpr.mm"
include "eqid.mm"
include "ovolgelb.mm"
include "syl3anc.mm"
include "c1st.mm"
include "c2nd.mm"
include "cif.mm"
include "cop.mm"
include "cmpt.mm"
include "simplll.mm"
include "adantr.mm"
include "simplr.mm"
include "wf.mm"
include "simprl.mm"
include "reex.mm"
include "xpex.mm"
include "inex2.mm"
include "nnex.mm"
include "elmap.mm"
include "sylib.mm"
include "simprrl.mm"
include "simprrr.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "ifbieq2d.mm"
include "breq12d.mm"
include "ifbieq12d.mm"
include "opeq12d.mm"
include "cbvmptv.mm"
include "ioombl1lem4.mm"
include "rexlimddv.mm"
include "ralrimiva.mm"
include "wb.mm"
include "inss1.mm"
include "ovolsscl.mm"
include "mp3an1.mm"
include "adantl.mm"
include "difss.mm"
include "readdcld.mm"
include "simprr.mm"
include "alrple.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "expr.mm"
include "sylan2.mm"
include "ismbl2.mm"
include "sylanbrc.mm"
include "c0.mm"
include "oveq1.mm"
include "iooid.mm"
include "syl6eq.mm"
include "0mbl.mm"
include "syl6eqel.mm"
include "ioomax.mm"
include "rembl.mm"
include "3jaoi.mm"
include "sylbi.mm"

theorem ioombl1
  let cA: class A
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. RR* -> ( A (,) +oo ) e. dom vol )

  proof
    cA
    cxr
    wcel
    cA
    cr
    wcel
    #
    cA
    cpnf
    wceq
    #
    cA
    cmnf
    wceq
    #
    w3o
    cA
    cpnf
    cioo
    co
    #
    cvol
    cdm
    #
    wcel
    #
    cA
    elxr
    @0
    @5
    @1
    @2
    @0
    @3
    cr
    wss
    #
    vx
    cv
    #
    covol
    cfv
    #
    cr
    wcel
    #
    @7
    @3
    cin
    #
    covol
    cfv
    #
    @7
    @3
    cdif
    #
    covol
    cfv
    #
    caddc
    co
    #
    @8
    cle
    wbr
    #
    wi
    #
    vx
    cr
    cpw
    #
    wral
    @5
    @6
    @0
    cA
    cpnf
    ioossre
    a1i
    @0
    @16
    vx
    @17
    @7
    @17
    wcel
    @0
    @7
    cr
    wss
    #
    @16
    @7
    cr
    elpwi
    @0
    @18
    @9
    @15
    @0
    @18
    @9
    wa
    #
    wa
    #
    @15
    @14
    @8
    vy
    cv
    #
    caddc
    co
    #
    cle
    wbr
    #
    vy
    crp
    wral
    #
    @20
    @23
    vy
    crp
    @20
    @21
    crp
    wcel
    #
    wa
    #
    @7
    cioo
    vf
    cv
    #
    ccom
    crn
    cuni
    wss
    #
    caddc
    cabs
    cmin
    ccom
    #
    @27
    ccom
    c1
    cseq
    #
    crn
    cxr
    clt
    csup
    @22
    cle
    wbr
    #
    wa
    #
    @23
    vf
    cle
    cr
    cr
    cxp
    #
    cin
    #
    cn
    cmap
    co
    #
    @26
    @18
    @9
    @25
    @32
    vf
    @35
    wrex
    @0
    @18
    @9
    @25
    simplrl
    #
    @0
    @18
    @9
    @25
    simplrr
    #
    @20
    @25
    simpr
    @7
    @21
    @30
    vf
    @30
    eqid
    #
    ovolgelb
    syl3anc
    @26
    @27
    @35
    wcel
    #
    @32
    wa
    #
    wa
    #
    cA
    @3
    @21
    vn
    cv
    #
    @27
    cfv
    #
    c1st
    cfv
    #
    @43
    c2nd
    cfv
    #
    @30
    caddc
    @29
    vm
    cn
    vm
    cv
    #
    @27
    cfv
    #
    c1st
    cfv
    #
    cA
    cle
    wbr
    #
    cA
    @48
    cif
    #
    @47
    c2nd
    cfv
    #
    cle
    wbr
    #
    @50
    @51
    cif
    #
    @51
    cop
    #
    cmpt
    #
    ccom
    c1
    cseq
    #
    caddc
    @29
    vm
    cn
    @48
    @53
    cop
    #
    cmpt
    #
    ccom
    c1
    cseq
    #
    vn
    @7
    @27
    @55
    @58
    @3
    eqid
    @0
    @19
    @25
    @40
    simplll
    @26
    @18
    @40
    @36
    adantr
    @26
    @9
    @40
    @37
    adantr
    @20
    @25
    @40
    simplr
    @38
    @56
    eqid
    @59
    eqid
    @41
    @39
    cn
    @34
    @27
    wf
    @26
    @39
    @32
    simprl
    @34
    cn
    @27
    @33
    cle
    cr
    cr
    reex
    reex
    xpex
    inex2
    nnex
    elmap
    sylib
    @26
    @39
    @28
    @31
    simprrl
    @26
    @39
    @28
    @31
    simprrr
    @44
    eqid
    @45
    eqid
    vm
    vn
    cn
    @54
    @44
    cA
    cle
    wbr
    #
    cA
    @44
    cif
    #
    @45
    cle
    wbr
    #
    @61
    @45
    cif
    #
    @45
    cop
    @46
    @42
    wceq
    #
    @53
    @63
    @51
    @45
    @64
    @52
    @62
    @50
    @51
    @61
    @45
    @64
    @50
    @61
    @51
    @45
    cle
    @64
    @49
    @60
    @48
    @44
    cA
    @64
    @48
    @44
    cA
    cle
    @64
    @47
    @43
    c1st
    @46
    @42
    @27
    fveq2
    #
    fveq2d
    #
    breq1d
    @66
    ifbieq2d
    #
    @64
    @47
    @43
    c2nd
    @65
    fveq2d
    #
    breq12d
    @67
    @68
    ifbieq12d
    #
    @68
    opeq12d
    cbvmptv
    vm
    vn
    cn
    @57
    @44
    @63
    cop
    @64
    @48
    @44
    @53
    @63
    @66
    @69
    opeq12d
    cbvmptv
    ioombl1lem4
    rexlimddv
    ralrimiva
    @20
    @14
    cr
    wcel
    @9
    @15
    @24
    wb
    @20
    @11
    @13
    @19
    @11
    cr
    wcel
    #
    @0
    @10
    @7
    wss
    @18
    @9
    @70
    @7
    @3
    inss1
    @10
    @7
    ovolsscl
    mp3an1
    adantl
    @19
    @13
    cr
    wcel
    #
    @0
    @12
    @7
    wss
    @18
    @9
    @71
    @7
    @3
    difss
    @12
    @7
    ovolsscl
    mp3an1
    adantl
    readdcld
    @0
    @18
    @9
    simprr
    vy
    @14
    @8
    alrple
    syl2anc
    mpbird
    expr
    sylan2
    ralrimiva
    vx
    @3
    ismbl2
    sylanbrc
    @1
    @3
    c0
    @4
    @1
    @3
    cpnf
    cpnf
    cioo
    co
    c0
    cA
    cpnf
    cpnf
    cioo
    oveq1
    cpnf
    iooid
    syl6eq
    0mbl
    syl6eqel
    @2
    @3
    cr
    @4
    @2
    @3
    cmnf
    cpnf
    cioo
    co
    cr
    cA
    cmnf
    cpnf
    cioo
    oveq1
    ioomax
    syl6eq
    rembl
    syl6eqel
    3jaoi
    sylbi
end
