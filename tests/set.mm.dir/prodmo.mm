include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "w3a.mm"
include "cz.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wf1o.mm"
include "wceq.mm"
include "cn.mm"
include "wo.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wmo.mm"
include "3simpb.mm"
include "reximi.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "seqeq1.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "cbvrexv.mm"
include "anbi2i.mm"
include "reeanv.mm"
include "bitr4i.mm"
include "wcel.mm"
include "simprlr.mm"
include "adantl.mm"
include "cc.mm"
include "adantlr.mm"
include "simprll.mm"
include "simprrl.mm"
include "prodrb.mm"
include "mpbid.mm"
include "simprrr.mm"
include "climuni.mm"
include "syl2anc.mm"
include "expcom.mm"
include "ex.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "syl2an.mm"
include "prodmolem2.mm"
include "equcomi.mm"
include "syl6.mm"
include "expimpd.mm"
include "com12.mm"
include "ancoms.mm"
include "csb.mm"
include "cmpt.mm"
include "eeanv.mm"
include "2rexbii.mm"
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
include "3bitr4i.mm"
include "an4.mm"
include "simpll.mm"
include "sylan.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "simplr.mm"
include "simprl.mm"
include "simprr.mm"
include "prodmolem3.mm"
include "eqeq12.mm"
include "syl5ibrcom.mm"
include "syl5bi.mm"
include "exlimdvv.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "ccase.mm"
include "alrimivv.mm"
include "breq2.mm"
include "3anbi3d.mm"
include "rexbidv.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "orbi12d.mm"
include "mo4.mm"
include "sylibr.mm"

theorem prodmo
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let va: setvar a
  let vg: setvar g
  let vw: setvar w
  let vz: setvar z
  assume prodmo.1: |- F = ( k e. ZZ |-> if ( k e. A , B , 1 ) )
  assume prodmo.2: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume prodmo.3: |- G = ( j e. NN |-> [_ ( f ` j ) / k ]_ B )

  disjoint A k
  disjoint A n
  disjoint k n
  disjoint F k
  disjoint F n
  disjoint k ph
  disjoint n ph
  disjoint A f
  disjoint A j
  disjoint A m
  disjoint A x
  disjoint B f
  disjoint B j
  disjoint B m
  disjoint F f
  disjoint f j
  disjoint F j
  disjoint f k
  disjoint f m
  disjoint F m
  disjoint f ph
  disjoint f x
  disjoint F x
  disjoint G j
  disjoint G x
  disjoint j k
  disjoint j m
  disjoint j ph
  disjoint j x
  disjoint k m
  disjoint k x
  disjoint m ph
  disjoint m x
  disjoint n x
  disjoint ph x
  disjoint x y
  disjoint M n
  disjoint N n
  disjoint A a
  disjoint a f
  disjoint a g
  disjoint A g
  disjoint a j
  disjoint a k
  disjoint a m
  disjoint a ph
  disjoint a w
  disjoint A w
  disjoint A z
  disjoint B a
  disjoint f g
  disjoint f w
  disjoint F w
  disjoint f z
  disjoint F z
  disjoint G a
  disjoint G g
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g ph
  disjoint g w
  disjoint G w
  disjoint g x
  disjoint g z
  disjoint G z
  disjoint j z
  disjoint k w
  disjoint k z
  disjoint m w
  disjoint m z
  disjoint n z
  disjoint ph w
  disjoint ph z
  disjoint w x
  disjoint w z
  disjoint x z
  disjoint y z
  assert |- ( ph -> E* x ( E. m e. ZZ ( A C_ ( ZZ>= ` m ) /\ E. n e. ( ZZ>= ` m ) E. y ( y =/= 0 /\ seq n ( x. , F ) ~~> y ) /\ seq m ( x. , F ) ~~> x ) \/ E. m e. NN E. f ( f : ( 1 ... m ) -1-1-onto-> A /\ x = ( seq 1 ( x. , G ) ` m ) ) ) )

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
    vy
    cv
    #
    cc0
    wne
    cmul
    cF
    vn
    cv
    cseq
    @3
    cli
    wbr
    wa
    vy
    wex
    vn
    @1
    wrex
    #
    cmul
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
    w3a
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
    @6
    @0
    cmul
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
    @4
    @5
    vz
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
    @12
    @20
    @14
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
    #
    vx
    vz
    weq
    #
    wi
    #
    vz
    wal
    vx
    wal
    @19
    vx
    wmo
    wph
    @31
    vx
    vz
    @29
    wph
    @30
    @9
    @23
    @18
    @27
    wph
    @30
    wi
    #
    @9
    @2
    @7
    wa
    #
    vm
    cz
    wrex
    #
    @2
    @21
    wa
    #
    vm
    cz
    wrex
    #
    @32
    @23
    @8
    @33
    vm
    cz
    @2
    @4
    @7
    3simpb
    reximi
    @22
    @35
    vm
    cz
    @2
    @4
    @21
    3simpb
    reximi
    @34
    @36
    wa
    #
    @33
    cA
    vw
    cv
    #
    cuz
    cfv
    #
    wss
    #
    cmul
    cF
    @38
    cseq
    #
    @20
    cli
    wbr
    #
    wa
    #
    wa
    #
    vw
    cz
    wrex
    vm
    cz
    wrex
    #
    @32
    @37
    @34
    @43
    vw
    cz
    wrex
    #
    wa
    @45
    @36
    @46
    @34
    @35
    @43
    vm
    vw
    cz
    vm
    vw
    weq
    #
    @2
    @40
    @21
    @42
    @47
    @1
    @39
    cA
    @0
    @38
    cuz
    fveq2
    sseq2d
    @47
    @5
    @41
    @20
    cli
    cmul
    cF
    @0
    @38
    seqeq1
    breq1d
    anbi12d
    cbvrexv
    anbi2i
    @33
    @43
    vm
    vw
    cz
    cz
    reeanv
    bitr4i
    @44
    @32
    vm
    vw
    cz
    cz
    @0
    cz
    wcel
    #
    @38
    cz
    wcel
    #
    wa
    #
    @44
    @32
    wph
    @50
    @44
    wa
    #
    @30
    wph
    @51
    wa
    #
    @41
    @6
    cli
    wbr
    #
    @42
    @30
    @52
    @7
    @53
    @51
    @7
    wph
    @50
    @2
    @7
    @43
    simprlr
    adantl
    @52
    cA
    cB
    @6
    vk
    cF
    @0
    @38
    prodmo.1
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
    @51
    prodmo.2
    adantlr
    wph
    @48
    @49
    @44
    simprll
    wph
    @48
    @49
    @44
    simprlr
    @51
    @2
    wph
    @50
    @2
    @7
    @43
    simprll
    adantl
    @51
    @40
    wph
    @50
    @33
    @40
    @42
    simprrl
    adantl
    prodrb
    mpbid
    @51
    @42
    wph
    @50
    @33
    @40
    @42
    simprrr
    adantl
    @6
    @20
    @41
    climuni
    syl2anc
    expcom
    ex
    rexlimivv
    sylbi
    syl2an
    @23
    @18
    @32
    wph
    @23
    @18
    wa
    @30
    wph
    @23
    @18
    @30
    wph
    @23
    wa
    @18
    vz
    vx
    weq
    @30
    wph
    vz
    vy
    vx
    cA
    cB
    vf
    vj
    vk
    vm
    vn
    cF
    cG
    prodmo.1
    prodmo.2
    prodmo.3
    prodmolem2
    vz
    vx
    equcomi
    syl6
    expimpd
    com12
    ancoms
    wph
    @9
    @27
    wa
    @30
    wph
    @9
    @27
    @30
    wph
    vx
    vy
    vz
    cA
    cB
    vf
    vj
    vk
    vm
    vn
    cF
    cG
    prodmo.1
    prodmo.2
    prodmo.3
    prodmolem2
    expimpd
    com12
    wph
    @18
    @27
    wa
    #
    @30
    @56
    @16
    c1
    @38
    cfz
    co
    #
    cA
    vg
    cv
    #
    wf1o
    #
    @20
    @38
    cmul
    vj
    cn
    vk
    vj
    cv
    #
    @58
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
    wa
    #
    vg
    wex
    vf
    wex
    #
    vw
    cn
    wrex
    vm
    cn
    wrex
    #
    wph
    @30
    @17
    @67
    vg
    wex
    #
    wa
    #
    vw
    cn
    wrex
    vm
    cn
    wrex
    @18
    @71
    vw
    cn
    wrex
    #
    wa
    @70
    @56
    @17
    @71
    vm
    vw
    cn
    cn
    reeanv
    @69
    @72
    vm
    vw
    cn
    cn
    @16
    @67
    vf
    vg
    eeanv
    2rexbii
    @27
    @73
    @18
    @26
    @71
    vm
    vw
    cn
    @47
    @26
    @57
    cA
    @11
    wf1o
    #
    @20
    @38
    @13
    cfv
    #
    wceq
    #
    wa
    #
    vf
    wex
    @71
    @47
    @25
    @77
    vf
    @47
    @12
    @74
    @24
    @76
    @47
    @10
    @57
    wceq
    @12
    @74
    wb
    @0
    @38
    c1
    cfz
    oveq2
    @10
    @57
    cA
    @11
    f1oeq2
    syl
    @47
    @14
    @75
    @20
    @0
    @38
    @13
    fveq2
    eqeq2d
    anbi12d
    exbidv
    @77
    @67
    vf
    vg
    vf
    vg
    weq
    #
    @74
    @59
    @76
    @66
    @57
    cA
    @11
    @58
    f1oeq1
    @78
    @75
    @65
    @20
    @78
    @38
    @13
    @64
    @78
    cG
    @63
    cmul
    c1
    @78
    cG
    vj
    cn
    vk
    @60
    @11
    cfv
    #
    cB
    csb
    #
    cmpt
    #
    @63
    prodmo.3
    @78
    vj
    cn
    @80
    @62
    @78
    vk
    @79
    @61
    cB
    @60
    @11
    @58
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
    anbi2i
    3bitr4i
    wph
    @69
    @30
    vm
    vw
    cn
    cn
    wph
    @0
    cn
    wcel
    @38
    cn
    wcel
    wa
    #
    wa
    #
    @68
    @30
    vf
    vg
    @68
    @12
    @59
    wa
    #
    @15
    @66
    wa
    #
    wa
    @83
    @30
    @12
    @15
    @59
    @66
    an4
    @83
    @84
    @85
    @30
    @83
    @84
    wa
    #
    @30
    @85
    @14
    @65
    wceq
    @86
    cA
    cB
    vf
    va
    vk
    cF
    cG
    @63
    @58
    @0
    @38
    prodmo.1
    @86
    wph
    @54
    @55
    wph
    @82
    @84
    simpll
    prodmo.2
    sylan
    cG
    @81
    va
    cn
    vk
    va
    cv
    #
    @11
    cfv
    #
    cB
    csb
    #
    cmpt
    prodmo.3
    vj
    va
    cn
    @80
    @89
    vj
    va
    weq
    #
    vk
    @79
    @88
    cB
    @60
    @87
    @11
    fveq2
    csbeq1d
    cbvmptv
    eqtri
    vj
    va
    cn
    @62
    vk
    @87
    @58
    cfv
    #
    cB
    csb
    @90
    vk
    @61
    @91
    cB
    @60
    @87
    @58
    fveq2
    csbeq1d
    cbvmptv
    wph
    @82
    @84
    simplr
    @83
    @12
    @59
    simprl
    @83
    @12
    @59
    simprr
    prodmolem3
    @6
    @14
    @20
    @65
    eqeq12
    syl5ibrcom
    expimpd
    syl5bi
    exlimdvv
    rexlimdvva
    syl5bir
    com12
    ccase
    com12
    alrimivv
    @19
    @28
    vx
    vz
    @30
    @9
    @23
    @18
    @27
    @30
    @8
    @22
    vm
    cz
    @30
    @7
    @21
    @2
    @4
    @6
    @20
    @5
    cli
    breq2
    3anbi3d
    rexbidv
    @30
    @17
    @26
    vm
    cn
    @30
    @16
    @25
    vf
    @30
    @15
    @24
    @12
    @6
    @20
    @14
    eqeq1
    anbi2d
    exbidv
    rexbidv
    orbi12d
    mo4
    sylibr
end
