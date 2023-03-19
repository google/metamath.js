include "cdvn.mm"
include "co.mm"
include "cfv.mm"
include "cfa.mm"
include "cv.mm"
include "cprod.mm"
include "cdiv.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "cpw.mm"
include "cn0.mm"
include "wceq.mm"
include "cc0.mm"
include "cfz.mm"
include "cmap.mm"
include "crab.mm"
include "fveq2.mm"
include "cbvsumv.mm"
include "eqeq1i.mm"
include "rabbii.mm"
include "fveq1.mm"
include "sumeq2ad.mm"
include "eqeq1d.mm"
include "cbvrabv.mm"
include "eqtri.mm"
include "mpteq2i.mm"
include "eqeq2.mm"
include "rabbidv.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "rabeq.mm"
include "syl.mm"
include "eqtrd.mm"
include "cbvmptv.mm"
include "sumeq1.mm"
include "mpteq2dv.mm"
include "dvnprodlem3.mm"
include "fveq2d.mm"
include "prodeq2ad.mm"
include "oveq2d.mm"
include "fveq1d.mm"
include "oveq12d.mm"
include "eqid.mm"
include "a1i.mm"

theorem dvnprod
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cC: class C
  let cS: class S
  let cT: class T
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cH: class H
  let cN: class N
  let cX: class X
  let vc: setvar c
  let ve: setvar e
  let vs: setvar s
  let vr: setvar r
  let vd: setvar d
  let vm: setvar m
  let vu: setvar u
  assume dvnprod.s: |- ( ph -> S e. { RR , CC } )
  assume dvnprod.x: |- ( ph -> X e. ( ( TopOpen ` CCfld ) |`t S ) )
  assume dvnprod.t: |- ( ph -> T e. Fin )
  assume dvnprod.h: |- ( ( ph /\ t e. T ) -> ( H ` t ) : X --> CC )
  assume dvnprod.n: |- ( ph -> N e. NN0 )
  assume dvnprod.dvnh: |- ( ( ph /\ t e. T /\ k e. ( 0 ... N ) ) -> ( ( S Dn ( H ` t ) ) ` k ) : X --> CC )
  assume dvnprod.f: |- F = ( x e. X |-> prod_ t e. T ( ( H ` t ) ` x ) )
  assume dvnprod.c: |- C = ( n e. NN0 |-> { c e. ( ( 0 ... n ) ^m T ) | sum_ t e. T ( c ` t ) = n } )

  disjoint C c
  disjoint H c
  disjoint H n
  disjoint H t
  disjoint H x
  disjoint c n
  disjoint c t
  disjoint c x
  disjoint n t
  disjoint n x
  disjoint t x
  disjoint H k
  disjoint k n
  disjoint k t
  disjoint k x
  disjoint N c
  disjoint N n
  disjoint N t
  disjoint N x
  disjoint N k
  disjoint S c
  disjoint S n
  disjoint S t
  disjoint S x
  disjoint S k
  disjoint T c
  disjoint T n
  disjoint T t
  disjoint T x
  disjoint T k
  disjoint X k
  disjoint X n
  disjoint X t
  disjoint X x
  disjoint k ph
  disjoint n ph
  disjoint ph t
  disjoint ph x
  disjoint k x
  disjoint C e
  disjoint c e
  disjoint F s
  disjoint H e
  disjoint e n
  disjoint e t
  disjoint e x
  disjoint H s
  disjoint e k
  disjoint e s
  disjoint k s
  disjoint n s
  disjoint s t
  disjoint s x
  disjoint N e
  disjoint N s
  disjoint S e
  disjoint S s
  disjoint T e
  disjoint T r
  disjoint T s
  disjoint e r
  disjoint k r
  disjoint n r
  disjoint r s
  disjoint r t
  disjoint r x
  disjoint X e
  disjoint X s
  disjoint d e
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint d r
  disjoint d s
  disjoint d t
  disjoint d x
  disjoint e m
  disjoint k m
  disjoint m n
  disjoint m r
  disjoint m s
  disjoint m t
  disjoint m x
  disjoint d u
  disjoint e u
  disjoint k u
  disjoint n u
  disjoint r u
  disjoint s u
  disjoint t u
  disjoint u x
  disjoint e ph
  disjoint ph s
  assert |- ( ph -> ( ( S Dn F ) ` N ) = ( x e. X |-> sum_ c e. ( C ` N ) ( ( ( ! ` N ) / prod_ t e. T ( ! ` ( c ` t ) ) ) x. prod_ t e. T ( ( ( S Dn ( H ` t ) ) ` ( c ` t ) ) ` x ) ) ) )

  proof
    wph
    cN
    cS
    cF
    cdvn
    co
    cfv
    vx
    cX
    cN
    cC
    cfv
    #
    cN
    cfa
    cfv
    #
    cT
    vt
    cv
    #
    ve
    cv
    #
    cfv
    #
    cfa
    cfv
    #
    vt
    cprod
    #
    cdiv
    co
    #
    cT
    vx
    cv
    #
    @4
    cS
    @2
    cH
    cfv
    cdvn
    co
    #
    cfv
    #
    cfv
    #
    vt
    cprod
    #
    cmul
    co
    #
    ve
    csu
    #
    cmpt
    #
    vx
    cX
    @0
    @1
    cT
    @2
    vc
    cv
    #
    cfv
    #
    cfa
    cfv
    #
    vt
    cprod
    #
    cdiv
    co
    #
    cT
    @8
    @17
    @9
    cfv
    #
    cfv
    #
    vt
    cprod
    #
    cmul
    co
    #
    vc
    csu
    #
    cmpt
    #
    wph
    vx
    vt
    cC
    vr
    cT
    cpw
    #
    vm
    cn0
    vr
    cv
    #
    vu
    cv
    #
    vd
    cv
    #
    cfv
    #
    vu
    csu
    #
    vm
    cv
    #
    wceq
    #
    vd
    cc0
    @33
    cfz
    co
    #
    @28
    cmap
    co
    #
    crab
    #
    cmpt
    #
    cmpt
    #
    cS
    cT
    vk
    vn
    cF
    cH
    cN
    cX
    vs
    ve
    dvnprod.s
    dvnprod.x
    dvnprod.t
    dvnprod.h
    dvnprod.n
    dvnprod.dvnh
    dvnprod.f
    @39
    vr
    @27
    vn
    cn0
    @28
    @4
    vt
    csu
    #
    vn
    cv
    #
    wceq
    #
    ve
    cc0
    @41
    cfz
    co
    #
    @28
    cmap
    co
    #
    crab
    #
    cmpt
    #
    cmpt
    vs
    @27
    vn
    cn0
    vs
    cv
    #
    @4
    vt
    csu
    #
    @41
    wceq
    #
    ve
    @43
    @47
    cmap
    co
    #
    crab
    #
    cmpt
    #
    cmpt
    vr
    @27
    @38
    @46
    @38
    vm
    cn0
    @40
    @33
    wceq
    #
    ve
    @36
    crab
    #
    cmpt
    @46
    vm
    cn0
    @37
    @54
    @37
    @28
    @2
    @30
    cfv
    #
    vt
    csu
    #
    @33
    wceq
    #
    vd
    @36
    crab
    @54
    @34
    @57
    vd
    @36
    @32
    @56
    @33
    @28
    @31
    @55
    vu
    vt
    @29
    @2
    @30
    fveq2
    cbvsumv
    eqeq1i
    rabbii
    @57
    @53
    vd
    ve
    @36
    @30
    @3
    wceq
    #
    @56
    @40
    @33
    @58
    @28
    @55
    @4
    vt
    @2
    @30
    @3
    fveq1
    sumeq2ad
    eqeq1d
    cbvrabv
    eqtri
    mpteq2i
    vm
    vn
    cn0
    @54
    @45
    @33
    @41
    wceq
    #
    @54
    @42
    ve
    @36
    crab
    #
    @45
    @59
    @53
    @42
    ve
    @36
    @33
    @41
    @40
    eqeq2
    rabbidv
    @59
    @36
    @44
    wceq
    @60
    @45
    wceq
    @59
    @35
    @43
    @28
    cmap
    @33
    @41
    cc0
    cfz
    oveq2
    oveq1d
    @42
    ve
    @36
    @44
    rabeq
    syl
    eqtrd
    cbvmptv
    eqtri
    mpteq2i
    vr
    vs
    @27
    @46
    @52
    @28
    @47
    wceq
    #
    vn
    cn0
    @45
    @51
    @61
    @45
    @49
    ve
    @44
    crab
    #
    @51
    @61
    @42
    @49
    ve
    @44
    @61
    @40
    @48
    @41
    @28
    @47
    @4
    vt
    sumeq1
    eqeq1d
    rabbidv
    @61
    @44
    @50
    wceq
    @62
    @51
    wceq
    @28
    @47
    @43
    cmap
    oveq2
    @49
    ve
    @44
    @50
    rabeq
    syl
    eqtrd
    mpteq2dv
    cbvmptv
    eqtri
    cC
    vn
    cn0
    cT
    @17
    vt
    csu
    #
    @41
    wceq
    #
    vc
    @43
    cT
    cmap
    co
    #
    crab
    #
    cmpt
    vn
    cn0
    cT
    @4
    vt
    csu
    #
    @41
    wceq
    #
    ve
    @65
    crab
    #
    cmpt
    dvnprod.c
    vn
    cn0
    @66
    @69
    @64
    @68
    vc
    ve
    @65
    @16
    @3
    wceq
    #
    @63
    @67
    @41
    @70
    cT
    @17
    @4
    vt
    @2
    @16
    @3
    fveq1
    sumeq2ad
    eqeq1d
    cbvrabv
    mpteq2i
    eqtri
    dvnprodlem3
    @15
    @26
    wceq
    wph
    vx
    cX
    @14
    @25
    @14
    @25
    @25
    @0
    @13
    @24
    ve
    vc
    @3
    @16
    wceq
    #
    @7
    @20
    @12
    @23
    cmul
    @71
    @6
    @19
    @1
    cdiv
    @71
    cT
    @5
    @18
    vt
    @71
    @4
    @17
    cfa
    @2
    @3
    @16
    fveq1
    #
    fveq2d
    prodeq2ad
    oveq2d
    @71
    cT
    @11
    @22
    vt
    @71
    @8
    @10
    @21
    @71
    @4
    @17
    @9
    @72
    fveq2d
    fveq1d
    prodeq2ad
    oveq12d
    cbvsumv
    @25
    eqid
    eqtri
    mpteq2i
    a1i
    eqtrd
end
