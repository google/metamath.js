include "ctop.mm"
include "wcel.mm"
include "cun.mm"
include "wceq.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "ccmp.mm"
include "cv.mm"
include "cuni.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "simpll.mm"
include "wss.mm"
include "wb.mm"
include "ssun1.mm"
include "sseq2.mm"
include "mpbiri.mm"
include "ad2antlr.mm"
include "cmpsub.mm"
include "syl2anc.mm"
include "simprr.mm"
include "sseqtrd.mm"
include "unieq.mm"
include "sseq2d.mm"
include "pweq.mm"
include "ineq1d.mm"
include "rexeqdv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "ad2antrl.mm"
include "mpid.mm"
include "sylbid.mm"
include "ssun2.mm"
include "reeanv.mm"
include "elin.mm"
include "simplbi.mm"
include "elpwid.mm"
include "anim12i.mm"
include "unss.mm"
include "sylib.mm"
include "simprbi.mm"
include "unfi.mm"
include "syl2an.mm"
include "jca.mm"
include "vex.mm"
include "elpw2.mm"
include "anbi1i.mm"
include "bitr2i.mm"
include "simpllr.mm"
include "ssun3.mm"
include "ssun4.mm"
include "ad2antll.mm"
include "eqsstrd.mm"
include "uniun.mm"
include "syl6sseqr.mm"
include "elpwi.mm"
include "adantr.mm"
include "sstrd.mm"
include "uniss.mm"
include "syl.mm"
include "eqssd.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "exp32.mm"
include "rexlimdvv.mm"
include "syl5bir.mm"
include "syl2and.mm"
include "impancom.mm"
include "expd.mm"
include "ralrimiv.mm"
include "iscmp.mm"
include "sylanbrc.mm"

theorem uncmp
  let cS: class S
  let cT: class T
  let cJ: class J
  let cX: class X
  let vc: setvar c
  let vd: setvar d
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vs: setvar s
  assume uncmp.1: |- X = U. J


  assert |- ( ( ( J e. Top /\ X = ( S u. T ) ) /\ ( ( J |`t S ) e. Comp /\ ( J |`t T ) e. Comp ) ) -> J e. Comp )

  proof
    cJ
    ctop
    wcel
    #
    cX
    cS
    cT
    cun
    #
    wceq
    #
    wa
    #
    cJ
    cS
    crest
    co
    ccmp
    wcel
    #
    cJ
    cT
    crest
    co
    ccmp
    wcel
    #
    wa
    #
    wa
    #
    @0
    cX
    vc
    cv
    #
    cuni
    #
    wceq
    #
    cX
    vd
    cv
    #
    cuni
    #
    wceq
    #
    vd
    @8
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vc
    cJ
    cpw
    #
    wral
    cJ
    ccmp
    wcel
    @0
    @2
    @6
    simpll
    @7
    @17
    vc
    @18
    @7
    @8
    @18
    wcel
    #
    @10
    @16
    @3
    @19
    @10
    wa
    #
    @6
    @16
    @3
    @20
    wa
    #
    @4
    cS
    vn
    cv
    #
    cuni
    #
    wss
    #
    vn
    @15
    wrex
    #
    @5
    cT
    vs
    cv
    #
    cuni
    #
    wss
    #
    vs
    @15
    wrex
    #
    @16
    @21
    @4
    cS
    vm
    cv
    #
    cuni
    #
    wss
    #
    @24
    vn
    @30
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vm
    @18
    wral
    #
    @25
    @21
    @0
    cS
    cX
    wss
    #
    @4
    @37
    wb
    @0
    @2
    @20
    simpll
    #
    @2
    @38
    @0
    @20
    @2
    @38
    cS
    @1
    wss
    cS
    cT
    ssun1
    cX
    @1
    cS
    sseq2
    mpbiri
    ad2antlr
    #
    cS
    cJ
    cX
    vm
    vn
    uncmp.1
    cmpsub
    syl2anc
    @21
    @37
    cS
    @9
    wss
    #
    @25
    @21
    cS
    cX
    @9
    @40
    @3
    @19
    @10
    simprr
    #
    sseqtrd
    @19
    @37
    @41
    @25
    wi
    #
    wi
    @3
    @10
    @36
    @43
    vm
    @8
    @18
    @30
    @8
    wceq
    #
    @32
    @41
    @35
    @25
    @44
    @31
    @9
    cS
    @30
    @8
    unieq
    sseq2d
    @44
    @24
    vn
    @34
    @15
    @44
    @33
    @14
    cfn
    @30
    @8
    pweq
    ineq1d
    rexeqdv
    imbi12d
    rspcv
    ad2antrl
    mpid
    sylbid
    @21
    @5
    cT
    vr
    cv
    #
    cuni
    #
    wss
    #
    @28
    vs
    @45
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vr
    @18
    wral
    #
    @29
    @21
    @0
    cT
    cX
    wss
    #
    @5
    @52
    wb
    @39
    @2
    @53
    @0
    @20
    @2
    @53
    cT
    @1
    wss
    cT
    cS
    ssun2
    cX
    @1
    cT
    sseq2
    mpbiri
    ad2antlr
    #
    cT
    cJ
    cX
    vr
    vs
    uncmp.1
    cmpsub
    syl2anc
    @21
    @52
    cT
    @9
    wss
    #
    @29
    @21
    cT
    cX
    @9
    @54
    @42
    sseqtrd
    @19
    @52
    @55
    @29
    wi
    #
    wi
    @3
    @10
    @51
    @56
    vr
    @8
    @18
    @45
    @8
    wceq
    #
    @47
    @55
    @50
    @29
    @57
    @46
    @9
    cT
    @45
    @8
    unieq
    sseq2d
    @57
    @28
    vs
    @49
    @15
    @57
    @48
    @14
    cfn
    @45
    @8
    pweq
    ineq1d
    rexeqdv
    imbi12d
    rspcv
    ad2antrl
    mpid
    sylbid
    @25
    @29
    wa
    @24
    @28
    wa
    #
    vs
    @15
    wrex
    vn
    @15
    wrex
    @21
    @16
    @24
    @28
    vn
    vs
    @15
    @15
    reeanv
    @21
    @58
    @16
    vn
    vs
    @15
    @15
    @21
    @22
    @15
    wcel
    #
    @26
    @15
    wcel
    #
    wa
    #
    @58
    @16
    @21
    @61
    @58
    wa
    #
    wa
    #
    @22
    @26
    cun
    #
    @15
    wcel
    #
    cX
    @64
    cuni
    #
    wceq
    #
    @16
    @63
    @64
    @8
    wss
    #
    @64
    cfn
    wcel
    #
    wa
    #
    @65
    @63
    @68
    @69
    @63
    @22
    @8
    wss
    #
    @26
    @8
    wss
    #
    wa
    #
    @68
    @61
    @73
    @21
    @58
    @59
    @71
    @60
    @72
    @59
    @22
    @8
    @59
    @22
    @14
    wcel
    #
    @22
    cfn
    wcel
    #
    @22
    @14
    cfn
    elin
    #
    simplbi
    elpwid
    @60
    @26
    @8
    @60
    @26
    @14
    wcel
    #
    @26
    cfn
    wcel
    #
    @26
    @14
    cfn
    elin
    #
    simplbi
    elpwid
    anim12i
    ad2antrl
    @22
    @26
    @8
    unss
    sylib
    #
    @61
    @69
    @21
    @58
    @59
    @75
    @78
    @69
    @60
    @59
    @74
    @75
    @76
    simprbi
    @60
    @77
    @78
    @79
    simprbi
    @22
    @26
    unfi
    syl2an
    ad2antrl
    jca
    @65
    @64
    @14
    wcel
    #
    @69
    wa
    @70
    @64
    @14
    cfn
    elin
    @81
    @68
    @69
    @64
    @8
    vc
    vex
    elpw2
    anbi1i
    bitr2i
    sylib
    @63
    cX
    @66
    @63
    cX
    @23
    @27
    cun
    #
    @66
    @63
    cX
    @1
    @82
    @0
    @2
    @20
    @62
    simpllr
    @63
    cS
    @82
    wss
    #
    cT
    @82
    wss
    #
    wa
    #
    @1
    @82
    wss
    @58
    @85
    @21
    @61
    @24
    @83
    @28
    @84
    cS
    @23
    @27
    ssun3
    cT
    @27
    @23
    ssun4
    anim12i
    ad2antll
    cS
    cT
    @82
    unss
    sylib
    eqsstrd
    @22
    @26
    uniun
    syl6sseqr
    @63
    @64
    cJ
    wss
    #
    @66
    cX
    wss
    @63
    @64
    @8
    cJ
    @80
    @20
    @8
    cJ
    wss
    #
    @3
    @62
    @19
    @87
    @10
    @8
    cJ
    elpwi
    adantr
    ad2antlr
    sstrd
    @86
    @66
    cJ
    cuni
    cX
    @64
    cJ
    uniss
    uncmp.1
    syl6sseqr
    syl
    eqssd
    @13
    @67
    vd
    @64
    @15
    @11
    @64
    wceq
    @12
    @66
    cX
    @11
    @64
    unieq
    eqeq2d
    rspcev
    syl2anc
    exp32
    rexlimdvv
    syl5bir
    syl2and
    impancom
    expd
    ralrimiv
    vc
    vd
    cJ
    cX
    uncmp.1
    iscmp
    sylanbrc
end
