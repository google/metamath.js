include "cin.mm"
include "wcel.mm"
include "cfv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "csu.mm"
include "c2.mm"
include "cexp.mm"
include "wceq.mm"
include "cbits.mm"
include "wrex.mm"
include "c1.mm"
include "cc0.mm"
include "cif.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "c2nd.mm"
include "c1st.mm"
include "cdm.mm"
include "cnvimass.mm"
include "cpr.mm"
include "cmap.mm"
include "wf.mm"
include "wa.mm"
include "wf1o.mm"
include "eulerpartgbij.mm"
include "f1of.mm"
include "ax-mp.mm"
include "ffvelrni.mm"
include "elin.mm"
include "sylib.mm"
include "simpld.mm"
include "elmapi.mm"
include "fdm.mm"
include "3syl.mm"
include "syl5sseq.mm"
include "sselda.mm"
include "eulerpartlemgvv.mm"
include "oveq1d.mm"
include "syldan.mm"
include "sumeq2dv.mm"
include "crab.mm"
include "weq.mm"
include "eqeq2.mm"
include "2rexbidv.mm"
include "elrab.mm"
include "simprbi.mm"
include "iftrued.mm"
include "elrabi.mm"
include "nncnd.mm"
include "mulid2d.mm"
include "eqtrd.mm"
include "sumeq2i.mm"
include "cres.mm"
include "id.mm"
include "cfn.mm"
include "cen.mm"
include "wbr.mm"
include "wss.mm"
include "eulerpartlemgf.mm"
include "adantl.mm"
include "1nn.mm"
include "syl6eqel.mm"
include "wb.mm"
include "wfn.mm"
include "syl.mm"
include "ffn.mm"
include "elpreima.mm"
include "adantr.mm"
include "mpbir2and.mm"
include "ex.mm"
include "ssrdv.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "cvv.mm"
include "wral.mm"
include "cnvexg.mm"
include "imaexg.mm"
include "inex1g.mm"
include "snex.mm"
include "fvex.mm"
include "xpex.mm"
include "rgenw.mm"
include "iunexg.mm"
include "sylancl.mm"
include "eqid.mm"
include "eulerpartlemgh.mm"
include "f1oeng.mm"
include "enfii.mm"
include "fvres.mm"
include "cn0.mm"
include "inss2.mm"
include "simpr.mm"
include "sseldi.mm"
include "snssd.mm"
include "bitsss.mm"
include "xpss12.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "oddpwdcv.mm"
include "fsumf1o.mm"
include "syl5eq.mm"
include "cc.mm"
include "ax-1cn.mm"
include "0cn.mm"
include "keepel.mm"
include "a1i.mm"
include "ssrab2.mm"
include "mulcld.mm"
include "cdif.mm"
include "wn.mm"
include "eldifbd.mm"
include "ssdifssd.mm"
include "wi.mm"
include "notbii.mm"
include "imnan.mm"
include "sylbb2.mm"
include "sylc.mm"
include "iffalsed.mm"
include "nnsscn.mm"
include "syl6ss.mm"
include "mul02d.mm"
include "fsumss.mm"
include "eqtr3d.mm"
include "eulerpartlemt0.mm"
include "simp1bi.mm"
include "inss1.mm"
include "sseldd.mm"
include "ffvelrnd.mm"
include "bitsfi.mm"
include "2cnd.mm"
include "simprr.mm"
include "expcld.mm"
include "anassrs.mm"
include "fsummulc1.mm"
include "bitsinv1.mm"
include "cop.mm"
include "vex.mm"
include "op2ndd.mm"
include "oveq2d.mm"
include "op1std.mm"
include "oveq12d.mm"
include "sseli.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "eleq1d.mm"
include "elab2g.mm"
include "mpbid.mm"
include "adantrr.mm"
include "fsum2d.mm"
include "3eqtr3d.mm"
include "sseq1d.mm"
include "elrab2.mm"
include "df-ss.mm"
include "sumeq1d.mm"
include "3eqtr2d.mm"
include "fveq2.mm"
include "cbvsumv.mm"
include "syl6eqr.mm"
include "0nn0.mm"
include "1nn0.mm"
include "prssi.mm"
include "mp2an.mm"
include "fss.mm"
include "mpan2.mm"
include "nn0ex.mm"
include "nnex.mm"
include "elmap.mm"
include "biimpri.mm"
include "anim1i.mm"
include "3imtr4i.mm"
include "eulerpartlemsv2.mm"
include "elind.mm"
include "3eqtr4d.mm"

theorem eulerpartlemgs2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vn: setvar n
  let vo: setvar o
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cM: class M
  let cN: class N
  let cO: class O
  let vr: setvar r
  let vt: setvar t
  let vm: setvar m
  let vw: setvar w
  assume eulerpart.p: |- P = { f e. ( NN0 ^m NN ) | ( ( `' f " NN ) e. Fin /\ sum_ k e. NN ( ( f ` k ) x. k ) = N ) }
  assume eulerpart.o: |- O = { g e. P | A. n e. ( `' g " NN ) -. 2 || n }
  assume eulerpart.d: |- D = { g e. P | A. n e. NN ( g ` n ) <_ 1 }
  assume eulerpart.j: |- J = { z e. NN | -. 2 || z }
  assume eulerpart.f: |- F = ( x e. J , y e. NN0 |-> ( ( 2 ^ y ) x. x ) )
  assume eulerpart.h: |- H = { r e. ( ( ~P NN0 i^i Fin ) ^m J ) | ( r supp (/) ) e. Fin }
  assume eulerpart.m: |- M = ( r e. H |-> { <. x , y >. | ( x e. J /\ y e. ( r ` x ) ) } )
  assume eulerpart.r: |- R = { f | ( `' f " NN ) e. Fin }
  assume eulerpart.t: |- T = { f e. ( NN0 ^m NN ) | ( `' f " NN ) C_ J }
  assume eulerpart.g: |- G = ( o e. ( T i^i R ) |-> ( ( _Ind ` NN ) ` ( F " ( M ` ( bits o. ( o |` J ) ) ) ) ) )
  assume eulerpart.s: |- S = ( f e. ( ( NN0 ^m NN ) i^i R ) |-> sum_ k e. NN ( ( f ` k ) x. k ) )

  disjoint f g
  disjoint f k
  disjoint f n
  disjoint f o
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g k
  disjoint g n
  disjoint g o
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint k n
  disjoint k o
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint n o
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint f r
  disjoint A f
  disjoint g r
  disjoint A g
  disjoint k r
  disjoint A k
  disjoint n r
  disjoint A n
  disjoint o r
  disjoint A o
  disjoint r x
  disjoint r y
  disjoint A r
  disjoint A x
  disjoint A y
  disjoint G f
  disjoint G k
  disjoint F n
  disjoint F o
  disjoint F x
  disjoint F y
  disjoint H o
  disjoint H r
  disjoint J f
  disjoint J n
  disjoint J o
  disjoint J r
  disjoint J x
  disjoint J y
  disjoint M n
  disjoint M o
  disjoint M r
  disjoint M x
  disjoint M y
  disjoint N f
  disjoint N g
  disjoint N k
  disjoint N n
  disjoint N x
  disjoint O n
  disjoint O r
  disjoint O x
  disjoint O y
  disjoint P g
  disjoint P k
  disjoint P n
  disjoint R f
  disjoint R k
  disjoint R n
  disjoint R o
  disjoint R r
  disjoint R x
  disjoint R y
  disjoint T f
  disjoint T k
  disjoint T n
  disjoint T o
  disjoint T r
  disjoint T x
  disjoint T y
  disjoint f t
  disjoint g t
  disjoint k t
  disjoint n t
  disjoint o t
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint f m
  disjoint f w
  disjoint g m
  disjoint g w
  disjoint k m
  disjoint k w
  disjoint m n
  disjoint m o
  disjoint m r
  disjoint m t
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n w
  disjoint o w
  disjoint r t
  disjoint r w
  disjoint t w
  disjoint A t
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint F t
  disjoint F w
  disjoint J t
  disjoint J w
  disjoint M t
  disjoint N t
  disjoint O t
  disjoint P t
  disjoint R t
  disjoint R w
  disjoint T t
  disjoint T w
  assert |- ( A e. ( T i^i R ) -> ( S ` ( G ` A ) ) = ( S ` A ) )

  proof
    cA
    cT
    cR
    cin
    #
    wcel
    #
    cA
    cG
    cfv
    #
    ccnv
    cn
    cima
    #
    vk
    cv
    #
    @2
    cfv
    #
    @4
    cmul
    co
    #
    vk
    csu
    #
    cA
    ccnv
    #
    cn
    cima
    #
    @4
    cA
    cfv
    #
    @4
    cmul
    co
    #
    vk
    csu
    #
    @2
    cS
    cfv
    #
    cA
    cS
    cfv
    #
    @1
    @7
    @9
    vt
    cv
    #
    cA
    cfv
    #
    @15
    cmul
    co
    #
    vt
    csu
    #
    @12
    @1
    @7
    @3
    c2
    vn
    cv
    #
    cexp
    co
    #
    @15
    cmul
    co
    #
    @4
    wceq
    #
    vn
    @16
    cbits
    cfv
    #
    wrex
    vt
    cn
    wrex
    #
    c1
    cc0
    cif
    #
    @4
    cmul
    co
    #
    vk
    csu
    #
    vt
    @9
    cJ
    cin
    #
    @15
    csn
    #
    @23
    cxp
    #
    ciun
    #
    c2
    vw
    cv
    #
    c2nd
    cfv
    #
    cexp
    co
    #
    @32
    c1st
    cfv
    #
    cmul
    co
    #
    vw
    csu
    #
    @18
    @1
    @3
    @6
    @26
    vk
    @1
    @4
    @3
    wcel
    #
    @4
    cn
    wcel
    #
    @6
    @26
    wceq
    @1
    @3
    cn
    @4
    @1
    @2
    cdm
    #
    @3
    cn
    @2
    cn
    cnvimass
    @1
    @2
    cc0
    c1
    cpr
    #
    cn
    cmap
    co
    #
    wcel
    #
    cn
    @41
    @2
    wf
    #
    @40
    cn
    wceq
    @1
    @43
    @2
    cR
    wcel
    #
    @1
    @2
    @42
    cR
    cin
    #
    wcel
    #
    @43
    @45
    wa
    #
    @0
    @46
    cA
    cG
    @0
    @46
    cG
    wf1o
    @0
    @46
    cG
    wf
    vx
    vy
    vz
    cD
    cP
    cR
    cT
    vf
    vg
    vk
    vn
    vo
    cF
    cG
    cH
    cJ
    cM
    cN
    cO
    vr
    eulerpart.p
    eulerpart.o
    eulerpart.d
    eulerpart.j
    eulerpart.f
    eulerpart.h
    eulerpart.m
    eulerpart.r
    eulerpart.t
    eulerpart.g
    eulerpartgbij
    @0
    @46
    cG
    f1of
    ax-mp
    ffvelrni
    #
    @2
    @42
    cR
    elin
    #
    sylib
    simpld
    #
    @2
    @41
    cn
    elmapi
    #
    cn
    @41
    @2
    fdm
    3syl
    syl5sseq
    #
    sselda
    @1
    @39
    wa
    @5
    @25
    @4
    cmul
    vx
    vy
    vz
    vt
    cA
    @4
    cD
    cP
    cR
    cT
    vf
    vg
    vk
    vn
    vo
    cF
    cG
    cH
    cJ
    cM
    cN
    cO
    vr
    eulerpart.p
    eulerpart.o
    eulerpart.d
    eulerpart.j
    eulerpart.f
    eulerpart.h
    eulerpart.m
    eulerpart.r
    eulerpart.t
    eulerpart.g
    eulerpartlemgvv
    #
    oveq1d
    syldan
    sumeq2dv
    @1
    @21
    vm
    cv
    #
    wceq
    #
    vn
    @23
    wrex
    vt
    cn
    wrex
    #
    vm
    cn
    crab
    #
    @26
    vk
    csu
    #
    @37
    @27
    @1
    @59
    @58
    @4
    vk
    csu
    @37
    @58
    @26
    @4
    vk
    @4
    @58
    wcel
    #
    @26
    c1
    @4
    cmul
    co
    @4
    @60
    @25
    c1
    @4
    cmul
    @60
    @24
    c1
    cc0
    @60
    @39
    @24
    @57
    @24
    vm
    @4
    cn
    vm
    vk
    weq
    @56
    @22
    vt
    vn
    cn
    @23
    @55
    @4
    @21
    eqeq2
    2rexbidv
    elrab
    #
    simprbi
    #
    iftrued
    oveq1d
    @60
    @4
    @60
    @4
    @57
    vm
    @4
    cn
    elrabi
    #
    nncnd
    mulid2d
    eqtrd
    sumeq2i
    @1
    @58
    @4
    @31
    @36
    vk
    vw
    cF
    @31
    cres
    #
    @36
    @4
    @36
    wceq
    id
    @1
    @58
    cfn
    wcel
    #
    @31
    @58
    cen
    wbr
    #
    @31
    cfn
    wcel
    @1
    @3
    cfn
    wcel
    @58
    @3
    wss
    @65
    vx
    vy
    vz
    cA
    cD
    cP
    cR
    cT
    vf
    vg
    vk
    vn
    vo
    cF
    cG
    cH
    cJ
    cM
    cN
    cO
    vr
    eulerpart.p
    eulerpart.o
    eulerpart.d
    eulerpart.j
    eulerpart.f
    eulerpart.h
    eulerpart.m
    eulerpart.r
    eulerpart.t
    eulerpart.g
    eulerpartlemgf
    #
    @1
    vk
    @58
    @3
    @1
    @60
    @38
    @1
    @60
    wa
    #
    @38
    @39
    @5
    cn
    wcel
    #
    @60
    @39
    @1
    @63
    adantl
    #
    @68
    @5
    c1
    cn
    @68
    @5
    @25
    c1
    @1
    @60
    @39
    @5
    @25
    wceq
    @70
    @54
    syldan
    @68
    @24
    c1
    cc0
    @60
    @24
    @1
    @62
    adantl
    iftrued
    eqtrd
    1nn
    syl6eqel
    @1
    @38
    @39
    @69
    wa
    wb
    #
    @60
    @1
    @44
    @2
    cn
    wfn
    @71
    @1
    @43
    @44
    @51
    @52
    syl
    cn
    @41
    @2
    ffn
    cn
    @4
    cn
    @2
    elpreima
    3syl
    adantr
    mpbir2and
    ex
    ssrdv
    #
    @3
    @58
    ssfi
    syl2anc
    @1
    @31
    cvv
    wcel
    #
    @31
    @58
    @64
    wf1o
    @66
    @1
    @28
    cvv
    wcel
    #
    @30
    cvv
    wcel
    #
    vt
    @28
    wral
    @73
    @1
    @8
    cvv
    wcel
    @9
    cvv
    wcel
    @74
    cA
    @0
    cnvexg
    @8
    cn
    cvv
    imaexg
    @9
    cJ
    cvv
    inex1g
    3syl
    @75
    vt
    @28
    @29
    @23
    @15
    snex
    @16
    cbits
    fvex
    xpex
    rgenw
    vt
    @28
    @30
    cvv
    cvv
    iunexg
    sylancl
    vx
    vy
    vz
    vt
    cA
    cD
    cP
    cR
    cT
    @31
    vf
    vg
    vk
    vm
    vn
    vo
    cF
    cG
    cH
    cJ
    cM
    cN
    cO
    vr
    eulerpart.p
    eulerpart.o
    eulerpart.d
    eulerpart.j
    eulerpart.f
    eulerpart.h
    eulerpart.m
    eulerpart.r
    eulerpart.t
    eulerpart.g
    @31
    eqid
    eulerpartlemgh
    #
    @31
    @58
    cvv
    @64
    f1oeng
    syl2anc
    @31
    @58
    enfii
    syl2anc
    @76
    @1
    @32
    @31
    wcel
    #
    wa
    #
    @32
    @64
    cfv
    #
    @32
    cF
    cfv
    #
    @36
    @77
    @79
    @80
    wceq
    @1
    @32
    @31
    cF
    fvres
    adantl
    @78
    @32
    cJ
    cn0
    cxp
    #
    wcel
    @80
    @36
    wceq
    @1
    @31
    @81
    @32
    @1
    @30
    @81
    wss
    #
    vt
    @28
    wral
    @31
    @81
    wss
    @1
    @82
    vt
    @28
    @1
    @15
    @28
    wcel
    #
    wa
    #
    @29
    cJ
    wss
    @23
    cn0
    wss
    @82
    @84
    @15
    cJ
    @84
    @28
    cJ
    @15
    @9
    cJ
    inss2
    @1
    @83
    simpr
    #
    sseldi
    snssd
    @16
    bitsss
    #
    @29
    cJ
    @23
    cn0
    xpss12
    sylancl
    ralrimiva
    vt
    @28
    @30
    @81
    iunss
    sylibr
    sselda
    vx
    vy
    vz
    cF
    cJ
    @32
    eulerpart.j
    eulerpart.f
    oddpwdcv
    syl
    eqtrd
    @68
    @4
    @70
    nncnd
    fsumf1o
    syl5eq
    @1
    @58
    @3
    @26
    vk
    @72
    @68
    @25
    @4
    @25
    cc
    wcel
    @68
    @24
    c1
    cc0
    cc
    ax-1cn
    0cn
    keepel
    a1i
    @68
    @4
    @68
    @58
    cn
    @4
    @57
    vm
    cn
    ssrab2
    @1
    @60
    simpr
    sseldi
    nncnd
    mulcld
    @1
    @4
    @3
    @58
    cdif
    #
    wcel
    #
    wa
    #
    @26
    cc0
    @4
    cmul
    co
    cc0
    @89
    @25
    cc0
    @4
    cmul
    @89
    @24
    c1
    cc0
    @89
    @60
    wn
    #
    @39
    @24
    wn
    #
    @89
    @4
    @3
    @58
    @1
    @88
    simpr
    eldifbd
    @1
    @87
    cn
    @4
    @1
    @3
    cn
    @58
    @53
    ssdifssd
    #
    sselda
    @90
    @39
    @24
    wa
    #
    wn
    @39
    @91
    wi
    @60
    @93
    @61
    notbii
    @39
    @24
    imnan
    sylbb2
    sylc
    iffalsed
    oveq1d
    @89
    @4
    @1
    @87
    cc
    @4
    @1
    @87
    cn
    cc
    @92
    nnsscn
    syl6ss
    sselda
    mul02d
    eqtrd
    @67
    fsumss
    eqtr3d
    @1
    @28
    @17
    vt
    csu
    #
    @37
    @18
    @1
    @28
    @23
    @20
    vn
    csu
    #
    @15
    cmul
    co
    #
    vt
    csu
    @28
    @23
    @21
    vn
    csu
    #
    vt
    csu
    @94
    @37
    @1
    @28
    @96
    @97
    vt
    @84
    @23
    @20
    @15
    vn
    @84
    @16
    cn0
    wcel
    #
    @23
    cfn
    wcel
    @84
    cn
    cn0
    @15
    cA
    @1
    cn
    cn0
    cA
    wf
    #
    @83
    @1
    cA
    cn0
    cn
    cmap
    co
    #
    wcel
    #
    @99
    @1
    @101
    @9
    cfn
    wcel
    #
    @9
    cJ
    wss
    #
    vx
    vy
    vz
    cA
    cD
    cP
    cR
    cT
    vf
    vg
    vk
    vn
    cF
    cH
    cJ
    cM
    cN
    cO
    vr
    eulerpart.p
    eulerpart.o
    eulerpart.d
    eulerpart.j
    eulerpart.f
    eulerpart.h
    eulerpart.m
    eulerpart.r
    eulerpart.t
    eulerpartlemt0
    simp1bi
    #
    cA
    cn0
    cn
    elmapi
    syl
    #
    adantr
    @84
    @9
    cn
    @15
    @1
    @9
    cn
    wss
    @83
    @1
    cA
    cdm
    #
    @9
    cn
    cA
    cn
    cnvimass
    @1
    @99
    @106
    cn
    wceq
    @105
    cn
    cn0
    cA
    fdm
    syl
    syl5sseq
    adantr
    @84
    @28
    @9
    @15
    @9
    cJ
    inss1
    #
    @85
    sseldi
    sseldd
    #
    ffvelrnd
    #
    @16
    bitsfi
    syl
    #
    @84
    @15
    @108
    nncnd
    #
    @1
    @83
    @19
    @23
    wcel
    #
    @20
    cc
    wcel
    @1
    @83
    @112
    wa
    wa
    #
    c2
    @19
    @113
    2cnd
    @113
    @23
    cn0
    @19
    @86
    @1
    @83
    @112
    simprr
    sseldi
    expcld
    #
    anassrs
    fsummulc1
    sumeq2dv
    @1
    @28
    @96
    @17
    vt
    @84
    @98
    @96
    @17
    wceq
    @109
    @98
    @95
    @16
    @15
    cmul
    vn
    @16
    bitsinv1
    oveq1d
    syl
    sumeq2dv
    @1
    vw
    @28
    @23
    @21
    @36
    vt
    vn
    @32
    @15
    @19
    cop
    wceq
    #
    @34
    @20
    @35
    @15
    cmul
    @115
    @33
    @19
    c2
    cexp
    @15
    @19
    @32
    vt
    vex
    #
    vn
    vex
    #
    op2ndd
    oveq2d
    @15
    @19
    @32
    @116
    @117
    op1std
    oveq12d
    @1
    @102
    @28
    @9
    wss
    @28
    cfn
    wcel
    @1
    cA
    cR
    wcel
    @102
    @0
    cR
    cA
    cT
    cR
    inss2
    sseli
    #
    vf
    cv
    #
    ccnv
    #
    cn
    cima
    #
    cfn
    wcel
    @102
    vf
    cA
    cR
    @0
    @119
    cA
    wceq
    #
    @121
    @9
    cfn
    @122
    @120
    @8
    cn
    @119
    cA
    cnveq
    imaeq1d
    #
    eleq1d
    eulerpart.r
    elab2g
    mpbid
    @107
    @9
    @28
    ssfi
    sylancl
    @110
    @113
    @20
    @15
    @114
    @1
    @83
    @15
    cc
    wcel
    @112
    @111
    adantrr
    mulcld
    fsum2d
    3eqtr3d
    @1
    @28
    @9
    @17
    vt
    @1
    @103
    @28
    @9
    wceq
    @1
    cA
    cT
    wcel
    #
    @103
    @0
    cT
    cA
    cT
    cR
    inss1
    sseli
    @124
    @101
    @103
    @121
    cJ
    wss
    @103
    vf
    cA
    @100
    cT
    @122
    @121
    @9
    cJ
    @123
    sseq1d
    eulerpart.t
    elrab2
    simprbi
    syl
    @9
    cJ
    df-ss
    sylib
    sumeq1d
    eqtr3d
    3eqtr2d
    @9
    @11
    @17
    vk
    vt
    vk
    vt
    weq
    #
    @10
    @16
    @4
    @15
    cmul
    @4
    @15
    cA
    fveq2
    @125
    id
    oveq12d
    cbvsumv
    syl6eqr
    @1
    @47
    @2
    @100
    cR
    cin
    #
    wcel
    #
    @13
    @7
    wceq
    @49
    @48
    @2
    @100
    wcel
    #
    @45
    wa
    @47
    @127
    @43
    @128
    @45
    @43
    @44
    cn
    cn0
    @2
    wf
    #
    @128
    @52
    @44
    @41
    cn0
    wss
    #
    @129
    cc0
    cn0
    wcel
    c1
    cn0
    wcel
    @130
    0nn0
    1nn0
    cc0
    c1
    cn0
    prssi
    mp2an
    cn
    @41
    cn0
    @2
    fss
    mpan2
    @128
    @129
    cn0
    cn
    @2
    nn0ex
    nnex
    elmap
    biimpri
    3syl
    anim1i
    @50
    @2
    @100
    cR
    elin
    3imtr4i
    @2
    cR
    cS
    vf
    vk
    eulerpart.r
    eulerpart.s
    eulerpartlemsv2
    3syl
    @1
    cA
    @126
    wcel
    @14
    @12
    wceq
    @1
    @100
    cR
    cA
    @104
    @118
    elind
    cA
    cR
    cS
    vf
    vk
    eulerpart.r
    eulerpart.s
    eulerpartlemsv2
    syl
    3eqtr4d
end
