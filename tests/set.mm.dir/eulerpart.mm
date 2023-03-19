include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "wss.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "cfn.mm"
include "wcel.mm"
include "cab.mm"
include "cin.mm"
include "cexp.mm"
include "cmul.mm"
include "cmpt2.mm"
include "cbits.mm"
include "cres.mm"
include "ccom.mm"
include "c0.mm"
include "csupp.mm"
include "cpw.mm"
include "cfv.mm"
include "wa.mm"
include "copab.mm"
include "cmpt.mm"
include "cind.mm"
include "wf1o.mm"
include "wex.mm"
include "chash.mm"
include "wceq.mm"
include "csu.mm"
include "eqid.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "cbvmpt2v.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "cbvrabv.mm"
include "eqcomi.mm"
include "fveq1.mm"
include "eleq2d.mm"
include "anbi2d.mm"
include "opabbidv.mm"
include "cbvmptv.mm"
include "simpl.mm"
include "simpr.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "anbi12d.mm"
include "cbvopabv.mm"
include "mpteq12i.mm"
include "eqtri.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "cbvabv.mm"
include "sseq1d.mm"
include "reseq1.mm"
include "coeq2d.mm"
include "imaeq2d.mm"
include "imaeq1i.mm"
include "3eqtr2i.mm"
include "fveq1i.mm"
include "imaeq2i.mm"
include "fveq2i.mm"
include "mpteq2i.mm"
include "eulerpartlemn.mm"
include "ovex.mm"
include "rabex.mm"
include "inex1.mm"
include "mptex.mm"
include "resex.mm"
include "f1oeq1.mm"
include "spcev.mm"
include "cen.mm"
include "bren.mm"
include "hasheni.mm"
include "sylbir.mm"
include "mp2b.mm"

theorem eulerpart
  let cD: class D
  let cP: class P
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vn: setvar n
  let cN: class N
  let cO: class O
  let va: setvar a
  let vb: setvar b
  let vh: setvar h
  let vm: setvar m
  let vo: setvar o
  let vq: setvar q
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume eulerpart.p: |- P = { f e. ( NN0 ^m NN ) | ( ( `' f " NN ) e. Fin /\ sum_ k e. NN ( ( f ` k ) x. k ) = N ) }
  assume eulerpart.o: |- O = { g e. P | A. n e. ( `' g " NN ) -. 2 || n }
  assume eulerpart.d: |- D = { g e. P | A. n e. NN ( g ` n ) <_ 1 }

  disjoint f g
  disjoint f k
  disjoint f n
  disjoint g k
  disjoint g n
  disjoint k n
  disjoint D g
  disjoint N f
  disjoint N g
  disjoint N k
  disjoint N n
  disjoint O g
  disjoint O n
  disjoint P g
  disjoint P k
  disjoint P n
  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a k
  disjoint a n
  disjoint a m
  disjoint a o
  disjoint a q
  disjoint a r
  disjoint a s
  disjoint a t
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b k
  disjoint b n
  disjoint b m
  disjoint b o
  disjoint b q
  disjoint b r
  disjoint b s
  disjoint b t
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint f h
  disjoint f m
  disjoint f o
  disjoint f q
  disjoint f r
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g h
  disjoint g m
  disjoint g o
  disjoint g q
  disjoint g r
  disjoint g s
  disjoint g t
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint h k
  disjoint h n
  disjoint h m
  disjoint h o
  disjoint h q
  disjoint h r
  disjoint h s
  disjoint h t
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint k m
  disjoint k o
  disjoint k q
  disjoint k r
  disjoint k s
  disjoint k t
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint m n
  disjoint n o
  disjoint n q
  disjoint n r
  disjoint n s
  disjoint n t
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint m o
  disjoint m q
  disjoint m r
  disjoint m s
  disjoint m t
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint o q
  disjoint o r
  disjoint o s
  disjoint o t
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint q r
  disjoint q s
  disjoint q t
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint r s
  disjoint r t
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint N q
  disjoint N x
  disjoint O r
  disjoint O x
  disjoint O y
  assert |- ( # ` O ) = ( # ` D )

  proof
    cO
    cD
    vo
    vh
    cv
    #
    ccnv
    #
    cn
    cima
    #
    c2
    vz
    cv
    cdvds
    wbr
    wn
    vz
    cn
    crab
    #
    wss
    #
    vh
    cn0
    cn
    cmap
    co
    #
    crab
    #
    @2
    cfn
    wcel
    #
    vh
    cab
    #
    cin
    #
    vx
    vy
    @3
    cn0
    c2
    vy
    cv
    #
    cexp
    co
    #
    vx
    cv
    #
    cmul
    co
    #
    cmpt2
    #
    cbits
    vo
    cv
    #
    @3
    cres
    #
    ccom
    #
    vr
    vr
    cv
    #
    c0
    csupp
    co
    #
    cfn
    wcel
    #
    vr
    cn0
    cpw
    cfn
    cin
    @3
    cmap
    co
    #
    crab
    #
    @12
    @3
    wcel
    #
    @10
    @12
    @18
    cfv
    #
    wcel
    #
    wa
    #
    vx
    vy
    copab
    #
    cmpt
    #
    cfv
    #
    cima
    #
    cn
    cind
    cfv
    #
    cfv
    #
    cmpt
    #
    cO
    cres
    #
    wf1o
    #
    cO
    cD
    vg
    cv
    #
    wf1o
    #
    vg
    wex
    #
    cO
    chash
    cfv
    cD
    chash
    cfv
    wceq
    #
    vx
    vy
    vz
    cD
    cP
    @8
    vf
    @5
    @8
    cin
    cn
    vk
    cv
    #
    vf
    cv
    #
    cfv
    @40
    cmul
    co
    vk
    csu
    cmpt
    #
    @6
    vf
    vg
    vk
    vn
    vq
    va
    vb
    @3
    cn0
    c2
    vb
    cv
    #
    cexp
    co
    #
    va
    cv
    #
    cmul
    co
    #
    cmpt2
    #
    @33
    vm
    cv
    #
    c0
    csupp
    co
    #
    cfn
    wcel
    #
    vm
    @21
    crab
    #
    @3
    vt
    vs
    cv
    #
    c0
    csupp
    co
    #
    cfn
    wcel
    #
    vs
    @21
    crab
    #
    @45
    @3
    wcel
    #
    @43
    @45
    vt
    cv
    #
    cfv
    #
    wcel
    #
    wa
    #
    va
    vb
    copab
    #
    cmpt
    #
    cN
    cO
    vr
    eulerpart.p
    eulerpart.o
    eulerpart.d
    @3
    eqid
    va
    vb
    vx
    vy
    @3
    cn0
    @46
    @13
    @44
    @12
    cmul
    co
    @45
    @12
    @44
    cmul
    oveq2
    @43
    @10
    wceq
    #
    @44
    @11
    @12
    cmul
    @43
    @10
    c2
    cexp
    oveq2
    oveq1d
    cbvmpt2v
    #
    @22
    @51
    @20
    @50
    vr
    vm
    @21
    @18
    @48
    wceq
    @19
    @49
    cfn
    @18
    @48
    c0
    csupp
    oveq1
    eleq1d
    cbvrabv
    #
    eqcomi
    @62
    vr
    @55
    @56
    @43
    @45
    @18
    cfv
    #
    wcel
    #
    wa
    #
    va
    vb
    copab
    #
    cmpt
    #
    vr
    @51
    @27
    cmpt
    #
    vt
    vr
    @55
    @61
    @69
    @57
    @18
    wceq
    #
    @60
    @68
    va
    vb
    @72
    @59
    @67
    @56
    @72
    @58
    @66
    @43
    @45
    @57
    @18
    fveq1
    eleq2d
    anbi2d
    opabbidv
    cbvmptv
    vr
    @55
    @69
    @51
    @27
    @51
    @55
    @50
    @54
    vm
    vs
    @21
    @48
    @52
    wceq
    @49
    @53
    cfn
    @48
    @52
    c0
    csupp
    oveq1
    eleq1d
    cbvrabv
    eqcomi
    @68
    @26
    va
    vb
    vx
    vy
    @45
    @12
    wceq
    #
    @63
    wa
    #
    @56
    @23
    @67
    @25
    @74
    @45
    @12
    @3
    @73
    @63
    simpl
    #
    eleq1d
    @74
    @43
    @10
    @66
    @24
    @73
    @63
    simpr
    @74
    @45
    @12
    @18
    @75
    fveq2d
    eleq12d
    anbi12d
    cbvopabv
    mpteq12i
    #
    eqtri
    @7
    @41
    ccnv
    #
    cn
    cima
    #
    cfn
    wcel
    vh
    vf
    @0
    @41
    wceq
    #
    @2
    @78
    cfn
    @79
    @1
    @77
    cn
    @0
    @41
    cnveq
    imaeq1d
    #
    eleq1d
    cbvabv
    @4
    @78
    @3
    wss
    vh
    vf
    @5
    @79
    @2
    @78
    @3
    @80
    sseq1d
    cbvrabv
    @33
    vq
    @9
    @14
    cbits
    vq
    cv
    #
    @3
    cres
    #
    ccom
    #
    @28
    cfv
    #
    cima
    #
    @31
    cfv
    #
    cmpt
    vq
    @9
    @47
    @83
    @62
    cfv
    #
    cima
    #
    @31
    cfv
    #
    cmpt
    vo
    vq
    @9
    @32
    @86
    @15
    @81
    wceq
    #
    @30
    @85
    @31
    @90
    @29
    @84
    @14
    @90
    @17
    @83
    @28
    @90
    @16
    @82
    cbits
    @15
    @81
    @3
    reseq1
    coeq2d
    fveq2d
    imaeq2d
    fveq2d
    cbvmptv
    vq
    @9
    @86
    @89
    @85
    @88
    @31
    @85
    @47
    @84
    cima
    @88
    @14
    @47
    @84
    @47
    @14
    @64
    eqcomi
    imaeq1i
    @84
    @87
    @47
    @83
    @28
    @62
    @28
    @71
    @70
    @62
    vr
    @22
    @27
    @51
    @27
    @65
    @27
    eqid
    mpteq12i
    @76
    vr
    vt
    @55
    @69
    @61
    @18
    @57
    wceq
    #
    @68
    @60
    va
    vb
    @91
    @67
    @59
    @56
    @91
    @66
    @58
    @43
    @45
    @18
    @57
    fveq1
    eleq2d
    anbi2d
    opabbidv
    cbvmptv
    3eqtr2i
    fveq1i
    imaeq2i
    eqtri
    fveq2i
    mpteq2i
    eqtri
    @42
    eqid
    eulerpartlemn
    @37
    @35
    vg
    @34
    @33
    cO
    vo
    @9
    @32
    @6
    @8
    @4
    vh
    @5
    cn0
    cn
    cmap
    ovex
    rabex
    inex1
    mptex
    resex
    cO
    cD
    @36
    @34
    f1oeq1
    spcev
    @38
    cO
    cD
    cen
    wbr
    @39
    cO
    cD
    vg
    bren
    cO
    cD
    hasheni
    sylbir
    mp2b
end
