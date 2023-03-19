include "cid.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cv.mm"
include "cuz.mm"
include "wss.mm"
include "caddc.mm"
include "cz.mm"
include "wcel.mm"
include "csb.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wf1o.mm"
include "cn.mm"
include "wex.mm"
include "wo.mm"
include "cio.mm"
include "csu.mm"
include "simpr.mm"
include "simplll.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nffv.mm"
include "nfeq.mm"
include "csbeq1a.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "rspc.mm"
include "sylc.mm"
include "ifeq1da.mm"
include "fvif.mm"
include "3eqtr4g.mm"
include "mpteq2dv.mm"
include "fveq1d.mm"
include "eqid.mm"
include "fvmptex.mm"
include "seqfeq.mm"
include "breq1d.mm"
include "anbi2d.mm"
include "rexbidva.mm"
include "simplr.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "wf.mm"
include "f1of.mm"
include "ad2antlr.mm"
include "ffvelrn.mm"
include "sylancom.mm"
include "cvv.mm"
include "fvex.mm"
include "csbfv2g.mm"
include "ax-mp.mm"
include "3eqtr3g.mm"
include "elfznn.mm"
include "adantl.mm"
include "fveq2.mm"
include "csbeq1d.mm"
include "fvmpti.mm"
include "syl.mm"
include "3eqtr4d.mm"
include "seqfveq.mm"
include "eqeq2d.mm"
include "pm5.32da.mm"
include "exbidv.mm"
include "orbi12d.mm"
include "iotabidv.mm"
include "df-sum.mm"

theorem sumeq2ii
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x

  disjoint A k
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint A f
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint B f
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint C f
  disjoint C m
  disjoint C n
  disjoint C x
  assert |- ( A. k e. A ( _I ` B ) = ( _I ` C ) -> sum_ k e. A B = sum_ k e. A C )

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
    caddc
    vn
    cz
    vn
    cv
    #
    cA
    wcel
    #
    vk
    @7
    cB
    csb
    #
    cc0
    cif
    #
    cmpt
    #
    @4
    cseq
    #
    vx
    cv
    #
    cli
    wbr
    #
    wa
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
    @13
    @4
    caddc
    vn
    cn
    vk
    @7
    @18
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
    caddc
    vn
    cz
    @8
    vk
    @7
    cC
    csb
    #
    cc0
    cif
    #
    cmpt
    #
    @4
    cseq
    #
    @13
    cli
    wbr
    #
    wa
    #
    vm
    cz
    wrex
    #
    @19
    @13
    @4
    caddc
    vn
    cn
    vk
    @20
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
    csu
    cA
    cC
    vk
    csu
    @3
    @28
    @43
    vx
    @3
    @16
    @35
    @27
    @42
    @3
    @15
    @34
    vm
    cz
    @3
    @4
    cz
    wcel
    #
    wa
    #
    @14
    @33
    @6
    @45
    @12
    @32
    @13
    cli
    @45
    caddc
    vx
    @11
    @31
    @4
    @3
    @44
    simpr
    @45
    @13
    @5
    wcel
    #
    wa
    #
    @13
    vn
    cz
    @10
    cid
    cfv
    #
    cmpt
    #
    cfv
    @13
    vn
    cz
    @30
    cid
    cfv
    #
    cmpt
    #
    cfv
    @13
    @11
    cfv
    @13
    @31
    cfv
    @47
    @13
    @49
    @51
    @47
    vn
    cz
    @48
    @50
    @47
    @8
    @9
    cid
    cfv
    #
    cc0
    cid
    cfv
    #
    cif
    @8
    @29
    cid
    cfv
    #
    @53
    cif
    @48
    @50
    @47
    @8
    @52
    @54
    @53
    @47
    @8
    wa
    @8
    @3
    @52
    @54
    wceq
    #
    @47
    @8
    simpr
    @3
    @44
    @46
    @8
    simplll
    @2
    @55
    vk
    @7
    cA
    vk
    @52
    @54
    vk
    @9
    cid
    vk
    cid
    nfcv
    #
    vk
    @7
    cB
    nfcsb1v
    nffv
    vk
    @29
    cid
    @56
    vk
    @7
    cC
    nfcsb1v
    nffv
    nfeq
    vk
    cv
    #
    @7
    wceq
    #
    @0
    @52
    @1
    @54
    @58
    cB
    @9
    cid
    vk
    @7
    cB
    csbeq1a
    fveq2d
    @58
    cC
    @29
    cid
    vk
    @7
    cC
    csbeq1a
    fveq2d
    eqeq12d
    rspc
    sylc
    ifeq1da
    @8
    @9
    cc0
    cid
    fvif
    @8
    @29
    cc0
    cid
    fvif
    3eqtr4g
    mpteq2dv
    fveq1d
    vn
    cz
    @10
    @13
    @11
    @49
    @11
    eqid
    @49
    eqid
    fvmptex
    vn
    cz
    @30
    @13
    @31
    @51
    @31
    eqid
    @51
    eqid
    fvmptex
    3eqtr4g
    seqfeq
    breq1d
    anbi2d
    rexbidva
    @3
    @26
    @41
    vm
    cn
    @3
    @4
    cn
    wcel
    #
    wa
    #
    @25
    @40
    vf
    @60
    @19
    @24
    @39
    @60
    @19
    wa
    #
    @23
    @38
    @13
    @61
    caddc
    vx
    @22
    @37
    c1
    @4
    @61
    @4
    cn
    c1
    cuz
    cfv
    @3
    @59
    @19
    simplr
    nnuz
    syl6eleq
    @61
    @13
    @17
    wcel
    #
    wa
    #
    vk
    @13
    @18
    cfv
    #
    cB
    csb
    #
    cid
    cfv
    #
    vk
    @64
    cC
    csb
    #
    cid
    cfv
    #
    @13
    @22
    cfv
    #
    @13
    @37
    cfv
    #
    @63
    vk
    @64
    @0
    csb
    #
    vk
    @64
    @1
    csb
    #
    @66
    @68
    @63
    @64
    cA
    wcel
    #
    @3
    @71
    @72
    wceq
    #
    @61
    @62
    @17
    cA
    @18
    wf
    #
    @73
    @19
    @75
    @60
    @62
    @17
    cA
    @18
    f1of
    ad2antlr
    @17
    cA
    @13
    @18
    ffvelrn
    sylancom
    @3
    @59
    @19
    @62
    simplll
    @2
    @74
    vk
    @64
    cA
    vk
    @71
    @72
    vk
    @64
    @0
    nfcsb1v
    vk
    @64
    @1
    nfcsb1v
    nfeq
    @57
    @64
    wceq
    @0
    @71
    @1
    @72
    vk
    @64
    @0
    csbeq1a
    vk
    @64
    @1
    csbeq1a
    eqeq12d
    rspc
    sylc
    @64
    cvv
    wcel
    #
    @71
    @66
    wceq
    @13
    @18
    fvex
    #
    vk
    @64
    cB
    cvv
    cid
    csbfv2g
    ax-mp
    @76
    @72
    @68
    wceq
    @77
    vk
    @64
    cC
    cvv
    cid
    csbfv2g
    ax-mp
    3eqtr3g
    @63
    @13
    cn
    wcel
    #
    @69
    @66
    wceq
    @62
    @78
    @61
    @13
    @4
    elfznn
    adantl
    #
    vn
    @13
    @21
    @65
    cn
    @22
    @7
    @13
    wceq
    #
    vk
    @20
    @64
    cB
    @7
    @13
    @18
    fveq2
    #
    csbeq1d
    @22
    eqid
    fvmpti
    syl
    @63
    @78
    @70
    @68
    wceq
    @79
    vn
    @13
    @36
    @67
    cn
    @37
    @80
    vk
    @20
    @64
    cC
    @81
    csbeq1d
    @37
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
    cA
    cB
    vf
    vk
    vm
    vn
    df-sum
    vx
    cA
    cC
    vf
    vk
    vm
    vn
    df-sum
    3eqtr4g
end
