include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "wa.mm"
include "cz.mm"
include "wrex.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wf1o.mm"
include "wceq.mm"
include "wex.mm"
include "cn.mm"
include "wo.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wmo.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "seqeq1.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "cbvrexv.mm"
include "reeanv.mm"
include "wcel.mm"
include "simprlr.mm"
include "cc.mm"
include "simpll.mm"
include "sylan.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simprll.mm"
include "simprrl.mm"
include "sumrb.mm"
include "mpbid.mm"
include "simprrr.mm"
include "climuni.mm"
include "syl2anc.mm"
include "exp31.mm"
include "rexlimdvv.mm"
include "syl5bir.mm"
include "expdimp.mm"
include "syl5bi.mm"
include "summolem2.mm"
include "jaod.mm"
include "equcom.mm"
include "syl6ib.mm"
include "impancom.mm"
include "csb.mm"
include "cmpt.mm"
include "wb.mm"
include "oveq2.mm"
include "f1oeq2.mm"
include "syl.mm"
include "eqeq2d.mm"
include "exbidv.mm"
include "f1oeq1.mm"
include "fveq1.mm"
include "csbeq1d.mm"
include "mpteq2dv.mm"
include "syl5eq.mm"
include "seqeq3d.mm"
include "fveq1d.mm"
include "cbvexv.mm"
include "syl6bb.mm"
include "eeanv.mm"
include "an4.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "simplr.mm"
include "simprl.mm"
include "simprr.mm"
include "summolem3.mm"
include "eqeq12.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "exlimdvv.mm"
include "rexlimdvva.mm"
include "jaodan.mm"
include "alrimivv.mm"
include "breq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "eqeq1.mm"
include "orbi12d.mm"
include "mo4.mm"
include "sylibr.mm"

theorem summo
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vg: setvar g
  let vi: setvar i
  let vj: setvar j
  let vy: setvar y
  let cH: class H
  let cK: class K
  let cN: class N
  let cM: class M
  assume summo.1: |- F = ( k e. ZZ |-> if ( k e. A , B , 0 ) )
  assume summo.2: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume summo.3: |- G = ( n e. NN |-> [_ ( f ` n ) / k ]_ B )

  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint A f
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint F f
  disjoint F k
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint G k
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint B f
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint ph x
  disjoint f ph
  disjoint f g
  disjoint f i
  disjoint f j
  disjoint f y
  disjoint g i
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint A i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint A j
  disjoint k y
  disjoint m y
  disjoint n y
  disjoint x y
  disjoint A y
  disjoint F g
  disjoint F j
  disjoint F y
  disjoint G g
  disjoint G i
  disjoint G j
  disjoint G y
  disjoint H i
  disjoint H x
  disjoint K i
  disjoint K j
  disjoint K k
  disjoint K m
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint N k
  disjoint N m
  disjoint N n
  disjoint g ph
  disjoint i ph
  disjoint j ph
  disjoint ph y
  disjoint B j
  disjoint B y
  disjoint M i
  disjoint M j
  disjoint M k
  disjoint M m
  disjoint M n
  disjoint M x
  disjoint M y
  assert |- ( ph -> E* x ( E. m e. ZZ ( A C_ ( ZZ>= ` m ) /\ seq m ( + , F ) ~~> x ) \/ E. m e. NN E. f ( f : ( 1 ... m ) -1-1-onto-> A /\ x = ( seq 1 ( + , G ) ` m ) ) ) )

  proof
    wph
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
    cF
    @0
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
    @0
    cfz
    co
    #
    cA
    vf
    cv
    #
    wf1o
    #
    @4
    @0
    caddc
    cG
    c1
    cseq
    #
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
    @2
    @3
    vy
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
    @10
    @18
    @12
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
    wa
    vx
    vy
    weq
    #
    wi
    #
    vy
    wal
    vx
    wal
    @17
    vx
    wmo
    wph
    @28
    vx
    vy
    wph
    @17
    @26
    @27
    wph
    @7
    @26
    @27
    wi
    @16
    wph
    @7
    wa
    #
    @21
    @27
    @25
    @21
    cA
    vn
    cv
    #
    cuz
    cfv
    #
    wss
    #
    caddc
    cF
    @30
    cseq
    #
    @18
    cli
    wbr
    #
    wa
    #
    vn
    cz
    wrex
    #
    @29
    @27
    @20
    @35
    vm
    vn
    cz
    vm
    vn
    weq
    #
    @2
    @32
    @19
    @34
    @37
    @1
    @31
    cA
    @0
    @30
    cuz
    fveq2
    sseq2d
    @37
    @3
    @33
    @18
    cli
    caddc
    cF
    @0
    @30
    seqeq1
    breq1d
    anbi12d
    cbvrexv
    wph
    @7
    @36
    @27
    @7
    @36
    wa
    @6
    @35
    wa
    #
    vn
    cz
    wrex
    vm
    cz
    wrex
    wph
    @27
    @6
    @35
    vm
    vn
    cz
    cz
    reeanv
    wph
    @38
    @27
    vm
    vn
    cz
    cz
    wph
    @0
    cz
    wcel
    #
    @30
    cz
    wcel
    #
    wa
    #
    @38
    @27
    wph
    @41
    wa
    #
    @38
    wa
    #
    @33
    @4
    cli
    wbr
    #
    @34
    @27
    @43
    @5
    @44
    @42
    @2
    @5
    @35
    simprlr
    @43
    cA
    cB
    @4
    vk
    cF
    @0
    @30
    summo.1
    @43
    wph
    vk
    cv
    cA
    wcel
    #
    cB
    cc
    wcel
    #
    wph
    @41
    @38
    simpll
    summo.2
    sylan
    wph
    @39
    @40
    @38
    simplrl
    wph
    @39
    @40
    @38
    simplrr
    @42
    @2
    @5
    @35
    simprll
    @42
    @6
    @32
    @34
    simprrl
    sumrb
    mpbid
    @42
    @6
    @32
    @34
    simprrr
    @4
    @18
    @33
    climuni
    syl2anc
    exp31
    rexlimdvv
    syl5bir
    expdimp
    syl5bi
    wph
    vx
    vy
    cA
    cB
    vf
    vk
    vm
    vn
    cF
    cG
    summo.1
    summo.2
    summo.3
    summolem2
    jaod
    wph
    @16
    wa
    #
    @21
    @27
    @25
    wph
    @21
    @16
    @27
    wph
    @21
    wa
    @16
    vy
    vx
    weq
    @27
    wph
    vy
    vx
    cA
    cB
    vf
    vk
    vm
    vn
    cF
    cG
    summo.1
    summo.2
    summo.3
    summolem2
    vy
    vx
    equcom
    syl6ib
    impancom
    @25
    c1
    @30
    cfz
    co
    #
    cA
    vg
    cv
    #
    wf1o
    #
    @18
    @30
    caddc
    vn
    cn
    vk
    @30
    @49
    cfv
    #
    cB
    csb
    #
    cmpt
    #
    c1
    cseq
    #
    cfv
    #
    wceq
    #
    wa
    #
    vg
    wex
    #
    vn
    cn
    wrex
    #
    @47
    @27
    @24
    @58
    vm
    vn
    cn
    @37
    @24
    @48
    cA
    @9
    wf1o
    #
    @18
    @30
    @11
    cfv
    #
    wceq
    #
    wa
    #
    vf
    wex
    @58
    @37
    @23
    @63
    vf
    @37
    @10
    @60
    @22
    @62
    @37
    @8
    @48
    wceq
    @10
    @60
    wb
    @0
    @30
    c1
    cfz
    oveq2
    @8
    @48
    cA
    @9
    f1oeq2
    syl
    @37
    @12
    @61
    @18
    @0
    @30
    @11
    fveq2
    eqeq2d
    anbi12d
    exbidv
    @63
    @57
    vf
    vg
    vf
    vg
    weq
    #
    @60
    @50
    @62
    @56
    @48
    cA
    @9
    @49
    f1oeq1
    @64
    @61
    @55
    @18
    @64
    @30
    @11
    @54
    @64
    cG
    @53
    caddc
    c1
    @64
    cG
    vn
    cn
    vk
    @30
    @9
    cfv
    #
    cB
    csb
    #
    cmpt
    #
    @53
    summo.3
    @64
    vn
    cn
    @66
    @52
    @64
    vk
    @65
    @51
    cB
    @30
    @9
    @49
    fveq1
    csbeq1d
    mpteq2dv
    syl5eq
    seqeq3d
    fveq1d
    eqeq2d
    anbi12d
    cbvexv
    syl6bb
    cbvrexv
    wph
    @16
    @59
    @27
    @16
    @59
    wa
    @15
    @58
    wa
    #
    vn
    cn
    wrex
    vm
    cn
    wrex
    wph
    @27
    @15
    @58
    vm
    vn
    cn
    cn
    reeanv
    wph
    @68
    @27
    vm
    vn
    cn
    cn
    @68
    @14
    @57
    wa
    #
    vg
    wex
    vf
    wex
    wph
    @0
    cn
    wcel
    @30
    cn
    wcel
    wa
    #
    wa
    #
    @27
    @14
    @57
    vf
    vg
    eeanv
    @71
    @69
    @27
    vf
    vg
    @69
    @10
    @50
    wa
    #
    @13
    @56
    wa
    #
    wa
    @71
    @27
    @10
    @13
    @50
    @56
    an4
    @71
    @72
    @73
    @27
    @71
    @72
    wa
    #
    @27
    @73
    @12
    @55
    wceq
    @74
    cA
    cB
    vf
    vk
    vj
    cF
    cG
    @53
    @49
    @0
    @30
    summo.1
    @74
    wph
    @45
    @46
    wph
    @70
    @72
    simpll
    summo.2
    sylan
    cG
    @67
    vj
    cn
    vk
    vj
    cv
    #
    @9
    cfv
    #
    cB
    csb
    #
    cmpt
    summo.3
    vn
    vj
    cn
    @66
    @77
    vn
    vj
    weq
    #
    vk
    @65
    @76
    cB
    @30
    @75
    @9
    fveq2
    csbeq1d
    cbvmptv
    eqtri
    vn
    vj
    cn
    @52
    vk
    @75
    @49
    cfv
    #
    cB
    csb
    @78
    vk
    @51
    @79
    cB
    @30
    @75
    @49
    fveq2
    csbeq1d
    cbvmptv
    wph
    @70
    @72
    simplr
    @71
    @10
    @50
    simprl
    @71
    @10
    @50
    simprr
    summolem3
    @4
    @12
    @18
    @55
    eqeq12
    syl5ibrcom
    expimpd
    syl5bi
    exlimdvv
    syl5bir
    rexlimdvva
    syl5bir
    expdimp
    syl5bi
    jaod
    jaodan
    expimpd
    alrimivv
    @17
    @26
    vx
    vy
    @27
    @7
    @21
    @16
    @25
    @27
    @6
    @20
    vm
    cz
    @27
    @5
    @19
    @2
    @4
    @18
    @3
    cli
    breq2
    anbi2d
    rexbidv
    @27
    @15
    @24
    vm
    cn
    @27
    @14
    @23
    vf
    @27
    @13
    @22
    @10
    @4
    @18
    @12
    eqeq1
    anbi2d
    exbidv
    rexbidv
    orbi12d
    mo4
    sylibr
end
