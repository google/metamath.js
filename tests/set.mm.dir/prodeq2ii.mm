include "cid.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cv.mm"
include "cuz.mm"
include "wss.mm"
include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "cif.mm"
include "cmpt.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "w3a.mm"
include "cfz.mm"
include "co.mm"
include "wf1o.mm"
include "cn.mm"
include "csb.mm"
include "wo.mm"
include "cio.mm"
include "cprod.mm"
include "wb.mm"
include "eluzelz.mm"
include "adantl.mm"
include "nfra1.mm"
include "wi.mm"
include "rsp.mm"
include "adantr.mm"
include "ifeq1.mm"
include "syl6.mm"
include "wn.mm"
include "iffalse.mm"
include "eqtr4d.mm"
include "pm2.61d1.mm"
include "fvif.mm"
include "3eqtr4g.mm"
include "mpteq2da.mm"
include "fveq1d.mm"
include "adantlr.mm"
include "eqid.mm"
include "fvmptex.mm"
include "seqfeq.mm"
include "breq1d.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "rexbidva.mm"
include "simpr.mm"
include "3anbi23d.mm"
include "simplr.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "wf.mm"
include "f1of.mm"
include "ad2antlr.mm"
include "ffvelrn.mm"
include "sylancom.mm"
include "simplll.mm"
include "nfcsb1v.mm"
include "nfeq.mm"
include "csbeq1a.mm"
include "eqeq12d.mm"
include "rspc.mm"
include "sylc.mm"
include "cvv.mm"
include "fvex.mm"
include "csbfv2g.mm"
include "ax-mp.mm"
include "3eqtr3g.mm"
include "elfznn.mm"
include "weq.mm"
include "fveq2.mm"
include "csbeq1d.mm"
include "fvmpti.mm"
include "syl.mm"
include "3eqtr4d.mm"
include "seqfveq.mm"
include "eqeq2d.mm"
include "pm5.32da.mm"
include "orbi12d.mm"
include "iotabidv.mm"
include "df-prod.mm"

theorem prodeq2ii
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y

  disjoint A k
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B f
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint C f
  disjoint C m
  disjoint C n
  disjoint C x
  disjoint C y
  assert |- ( A. k e. A ( _I ` B ) = ( _I ` C ) -> prod_ k e. A B = prod_ k e. A C )

  proof
    cB
    cid
    cfv
    #
    cC
    cid
    cfv
    #
    wceq
    #
    vk
    cA
    wral
    #
    cA
    vm
    cv
    #
    cuz
    cfv
    #
    wss
    #
    vy
    cv
    #
    cc0
    wne
    #
    cmul
    vk
    cz
    vk
    cv
    #
    cA
    wcel
    #
    cB
    c1
    cif
    #
    cmpt
    #
    vn
    cv
    #
    cseq
    #
    @7
    cli
    wbr
    #
    wa
    #
    vy
    wex
    #
    vn
    @5
    wrex
    #
    cmul
    @12
    @4
    cseq
    #
    vx
    cv
    #
    cli
    wbr
    #
    w3a
    #
    vm
    cz
    wrex
    #
    c1
    @4
    cfz
    co
    #
    cA
    vf
    cv
    #
    wf1o
    #
    @20
    @4
    cmul
    vn
    cn
    vk
    @13
    @25
    cfv
    #
    cB
    csb
    #
    cmpt
    #
    c1
    cseq
    cfv
    #
    wceq
    #
    wa
    #
    vf
    wex
    #
    vm
    cn
    wrex
    #
    wo
    #
    vx
    cio
    @6
    @8
    cmul
    vk
    cz
    @10
    cC
    c1
    cif
    #
    cmpt
    #
    @13
    cseq
    #
    @7
    cli
    wbr
    #
    wa
    #
    vy
    wex
    #
    vn
    @5
    wrex
    #
    cmul
    @37
    @4
    cseq
    #
    @20
    cli
    wbr
    #
    w3a
    #
    vm
    cz
    wrex
    #
    @26
    @20
    @4
    cmul
    vn
    cn
    vk
    @27
    cC
    csb
    #
    cmpt
    #
    c1
    cseq
    cfv
    #
    wceq
    #
    wa
    #
    vf
    wex
    #
    vm
    cn
    wrex
    #
    wo
    #
    vx
    cio
    cA
    cB
    vk
    cprod
    cA
    cC
    vk
    cprod
    @3
    @35
    @54
    vx
    @3
    @23
    @46
    @34
    @53
    @3
    @22
    @45
    vm
    cz
    @3
    @4
    cz
    wcel
    #
    wa
    #
    @18
    @42
    @21
    @44
    @6
    @3
    @18
    @42
    wb
    @55
    @3
    @17
    @41
    vn
    @5
    @3
    @13
    @5
    wcel
    #
    wa
    #
    @16
    @40
    vy
    @58
    @15
    @39
    @8
    @58
    @14
    @38
    @7
    cli
    @58
    cmul
    vx
    @12
    @37
    @13
    @57
    @13
    cz
    wcel
    @3
    @4
    @13
    eluzelz
    adantl
    @58
    @20
    @13
    cuz
    cfv
    wcel
    #
    wa
    @20
    vk
    cz
    @11
    cid
    cfv
    #
    cmpt
    #
    cfv
    #
    @20
    vk
    cz
    @36
    cid
    cfv
    #
    cmpt
    #
    cfv
    #
    @20
    @12
    cfv
    #
    @20
    @37
    cfv
    #
    @3
    @59
    @62
    @65
    wceq
    @57
    @3
    @59
    wa
    @20
    @61
    @64
    @3
    @61
    @64
    wceq
    #
    @59
    @3
    vk
    cz
    @60
    @63
    @2
    vk
    cA
    nfra1
    @3
    @9
    cz
    wcel
    #
    wa
    #
    @10
    @0
    c1
    cid
    cfv
    #
    cif
    #
    @10
    @1
    @71
    cif
    #
    @60
    @63
    @70
    @10
    @72
    @73
    wceq
    #
    @70
    @10
    @2
    @74
    @3
    @10
    @2
    wi
    @69
    @2
    vk
    cA
    rsp
    adantr
    @10
    @0
    @1
    @71
    ifeq1
    syl6
    @10
    wn
    @72
    @71
    @73
    @10
    @0
    @71
    iffalse
    @10
    @1
    @71
    iffalse
    eqtr4d
    pm2.61d1
    @10
    cB
    c1
    cid
    fvif
    @10
    cC
    c1
    cid
    fvif
    3eqtr4g
    mpteq2da
    #
    adantr
    fveq1d
    adantlr
    vk
    cz
    @11
    @20
    @12
    @61
    @12
    eqid
    @61
    eqid
    fvmptex
    #
    vk
    cz
    @36
    @20
    @37
    @64
    @37
    eqid
    @64
    eqid
    fvmptex
    #
    3eqtr4g
    seqfeq
    breq1d
    anbi2d
    exbidv
    rexbidva
    adantr
    @56
    @19
    @43
    @20
    cli
    @56
    cmul
    vx
    @12
    @37
    @4
    @3
    @55
    simpr
    @3
    @20
    @5
    wcel
    #
    @66
    @67
    wceq
    @55
    @3
    @78
    wa
    #
    @62
    @65
    @66
    @67
    @79
    @20
    @61
    @64
    @3
    @68
    @78
    @75
    adantr
    fveq1d
    @76
    @77
    3eqtr4g
    adantlr
    seqfeq
    breq1d
    3anbi23d
    rexbidva
    @3
    @33
    @52
    vm
    cn
    @3
    @4
    cn
    wcel
    #
    wa
    #
    @32
    @51
    vf
    @81
    @26
    @31
    @50
    @81
    @26
    wa
    #
    @30
    @49
    @20
    @82
    cmul
    vx
    @29
    @48
    c1
    @4
    @82
    @4
    cn
    c1
    cuz
    cfv
    @3
    @80
    @26
    simplr
    nnuz
    syl6eleq
    @82
    @20
    @24
    wcel
    #
    wa
    #
    vk
    @20
    @25
    cfv
    #
    cB
    csb
    #
    cid
    cfv
    #
    vk
    @85
    cC
    csb
    #
    cid
    cfv
    #
    @20
    @29
    cfv
    #
    @20
    @48
    cfv
    #
    @84
    vk
    @85
    @0
    csb
    #
    vk
    @85
    @1
    csb
    #
    @87
    @89
    @84
    @85
    cA
    wcel
    #
    @3
    @92
    @93
    wceq
    #
    @82
    @83
    @24
    cA
    @25
    wf
    #
    @94
    @26
    @96
    @81
    @83
    @24
    cA
    @25
    f1of
    ad2antlr
    @24
    cA
    @20
    @25
    ffvelrn
    sylancom
    @3
    @80
    @26
    @83
    simplll
    @2
    @95
    vk
    @85
    cA
    vk
    @92
    @93
    vk
    @85
    @0
    nfcsb1v
    vk
    @85
    @1
    nfcsb1v
    nfeq
    @9
    @85
    wceq
    @0
    @92
    @1
    @93
    vk
    @85
    @0
    csbeq1a
    vk
    @85
    @1
    csbeq1a
    eqeq12d
    rspc
    sylc
    @85
    cvv
    wcel
    #
    @92
    @87
    wceq
    @20
    @25
    fvex
    #
    vk
    @85
    cB
    cvv
    cid
    csbfv2g
    ax-mp
    @97
    @93
    @89
    wceq
    @98
    vk
    @85
    cC
    cvv
    cid
    csbfv2g
    ax-mp
    3eqtr3g
    @84
    @20
    cn
    wcel
    #
    @90
    @87
    wceq
    @83
    @99
    @82
    @20
    @4
    elfznn
    adantl
    #
    vn
    @20
    @28
    @86
    cn
    @29
    vn
    vx
    weq
    #
    vk
    @27
    @85
    cB
    @13
    @20
    @25
    fveq2
    #
    csbeq1d
    @29
    eqid
    fvmpti
    syl
    @84
    @99
    @91
    @89
    wceq
    @100
    vn
    @20
    @47
    @88
    cn
    @48
    @101
    vk
    @27
    @85
    cC
    @102
    csbeq1d
    @48
    eqid
    fvmpti
    syl
    3eqtr4d
    seqfveq
    eqeq2d
    pm5.32da
    exbidv
    rexbidva
    orbi12d
    iotabidv
    vx
    vy
    cA
    cB
    vf
    vk
    vm
    vn
    df-prod
    vx
    vy
    cA
    cC
    vf
    vk
    vm
    vn
    df-prod
    3eqtr4g
end
