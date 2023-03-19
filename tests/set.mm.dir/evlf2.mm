include "cop.mm"
include "c2nd.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "c1st.mm"
include "cmpt2.mm"
include "cfunc.mm"
include "cxp.mm"
include "csb.mm"
include "cvv.mm"
include "wceq.mm"
include "evlfval.mm"
include "ovex.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "xpex.mm"
include "op2ndd.mm"
include "syl.mm"
include "wa.mm"
include "fvexd.mm"
include "simprl.mm"
include "fveq2d.mm"
include "wcel.mm"
include "op1stg.mm"
include "syl2anc.mm"
include "adantr.mm"
include "eqtrd.mm"
include "simplrr.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simpr.mm"
include "oveq12d.mm"
include "op2ndg.mm"
include "ad3antrrr.mm"
include "fveq12d.mm"
include "opeq12d.mm"
include "oveq123d.mm"
include "fveq1d.mm"
include "mpt2eq123dv.mm"
include "csbied2.mm"
include "opelxpi.mm"
include "a1i.mm"
include "ovmpt2d.mm"
include "syl5eq.mm"

theorem evlf2
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let c.x: class .x.
  let vg: setvar g
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cL: class L
  let cN: class N
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let ve: setvar e
  let vz: setvar z
  let cA: class A
  let cK: class K
  assume evlfval.e: |- E = ( C evalF D )
  assume evlfval.c: |- ( ph -> C e. Cat )
  assume evlfval.d: |- ( ph -> D e. Cat )
  assume evlfval.b: |- B = ( Base ` C )
  assume evlfval.h: |- H = ( Hom ` C )
  assume evlfval.o: |- .x. = ( comp ` D )
  assume evlfval.n: |- N = ( C Nat D )
  assume evlf2.f: |- ( ph -> F e. ( C Func D ) )
  assume evlf2.g: |- ( ph -> G e. ( C Func D ) )
  assume evlf2.x: |- ( ph -> X e. B )
  assume evlf2.y: |- ( ph -> Y e. B )
  assume evlf2.l: |- L = ( <. F , X >. ( 2nd ` E ) <. G , Y >. )

  disjoint a g
  disjoint C a
  disjoint C g
  disjoint D a
  disjoint D g
  disjoint H g
  disjoint F a
  disjoint F g
  disjoint N a
  disjoint N g
  disjoint G a
  disjoint G g
  disjoint a ph
  disjoint g ph
  disjoint .x. a
  disjoint .x. g
  disjoint X a
  disjoint X g
  disjoint Y a
  disjoint Y g
  disjoint a c
  disjoint a d
  disjoint a f
  disjoint a m
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint c d
  disjoint c f
  disjoint c g
  disjoint c m
  disjoint c n
  disjoint c x
  disjoint c y
  disjoint C c
  disjoint d f
  disjoint d g
  disjoint d m
  disjoint d n
  disjoint d x
  disjoint d y
  disjoint C d
  disjoint f g
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint C f
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint C m
  disjoint n x
  disjoint n y
  disjoint C n
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint D c
  disjoint D d
  disjoint D f
  disjoint D m
  disjoint D n
  disjoint D x
  disjoint D y
  disjoint H c
  disjoint H d
  disjoint H m
  disjoint H n
  disjoint H x
  disjoint H y
  disjoint a e
  disjoint a z
  disjoint c e
  disjoint c z
  disjoint d e
  disjoint d z
  disjoint e f
  disjoint e g
  disjoint e m
  disjoint e n
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint f z
  disjoint g z
  disjoint m z
  disjoint n z
  disjoint x z
  disjoint y z
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint N c
  disjoint N d
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint c ph
  disjoint d ph
  disjoint f ph
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint .x. c
  disjoint .x. d
  disjoint .x. m
  disjoint .x. n
  disjoint .x. x
  disjoint .x. y
  disjoint A a
  disjoint A g
  disjoint B c
  disjoint B d
  disjoint B x
  disjoint B y
  disjoint X m
  disjoint X n
  disjoint X x
  disjoint X y
  disjoint Y m
  disjoint Y n
  disjoint Y x
  disjoint Y y
  disjoint K a
  disjoint K g
  assert |- ( ph -> L = ( a e. ( F N G ) , g e. ( X H Y ) |-> ( ( a ` Y ) ( <. ( ( 1st ` F ) ` X ) , ( ( 1st ` F ) ` Y ) >. .x. ( ( 1st ` G ) ` Y ) ) ( ( X ( 2nd ` F ) Y ) ` g ) ) ) )

  proof
    wph
    cL
    cF
    cX
    cop
    #
    cG
    cY
    cop
    #
    cE
    c2nd
    cfv
    #
    co
    va
    vg
    cF
    cG
    cN
    co
    #
    cX
    cY
    cH
    co
    #
    cY
    va
    cv
    #
    cfv
    #
    vg
    cv
    #
    cX
    cY
    cF
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    cX
    cF
    c1st
    cfv
    #
    cfv
    #
    cY
    @11
    cfv
    #
    cop
    #
    cY
    cG
    c1st
    cfv
    #
    cfv
    #
    c.x
    co
    #
    co
    #
    cmpt2
    #
    evlf2.l
    wph
    vx
    vy
    @0
    @1
    cC
    cD
    cfunc
    co
    #
    cB
    cxp
    #
    @21
    vm
    vx
    cv
    #
    c1st
    cfv
    #
    vn
    vy
    cv
    #
    c1st
    cfv
    #
    va
    vg
    vm
    cv
    #
    vn
    cv
    #
    cN
    co
    #
    @22
    c2nd
    cfv
    #
    @24
    c2nd
    cfv
    #
    cH
    co
    #
    @30
    @5
    cfv
    #
    @7
    @29
    @30
    @26
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    @29
    @26
    c1st
    cfv
    #
    cfv
    #
    @30
    @36
    cfv
    #
    cop
    #
    @30
    @27
    c1st
    cfv
    #
    cfv
    #
    c.x
    co
    #
    co
    #
    cmpt2
    #
    csb
    #
    csb
    #
    @19
    @2
    cvv
    wph
    cE
    vf
    vx
    @20
    cB
    @22
    vf
    cv
    c1st
    cfv
    cfv
    #
    cmpt2
    #
    vx
    vy
    @21
    @21
    @46
    cmpt2
    #
    cop
    wceq
    @2
    @49
    wceq
    wph
    vx
    vy
    cB
    cC
    cD
    c.x
    vf
    vg
    vm
    vn
    cE
    cH
    cN
    va
    evlfval.e
    evlfval.c
    evlfval.d
    evlfval.b
    evlfval.h
    evlfval.o
    evlfval.n
    evlfval
    @48
    @49
    cE
    vf
    vx
    @20
    cB
    @47
    cC
    cD
    cfunc
    ovex
    #
    cB
    cC
    cbs
    cfv
    cvv
    evlfval.b
    cC
    cbs
    fvex
    eqeltri
    #
    mpt2ex
    vx
    vy
    @21
    @21
    @46
    @20
    cB
    @50
    @51
    xpex
    #
    @52
    mpt2ex
    op2ndd
    syl
    wph
    @22
    @0
    wceq
    #
    @24
    @1
    wceq
    #
    wa
    #
    wa
    #
    vm
    @23
    cF
    @45
    @19
    cvv
    @56
    @22
    c1st
    fvexd
    @56
    @23
    @0
    c1st
    cfv
    #
    cF
    @56
    @22
    @0
    c1st
    wph
    @53
    @54
    simprl
    #
    fveq2d
    wph
    @57
    cF
    wceq
    #
    @55
    wph
    cF
    @20
    wcel
    #
    cX
    cB
    wcel
    #
    @59
    evlf2.f
    evlf2.x
    cF
    cX
    @20
    cB
    op1stg
    syl2anc
    adantr
    eqtrd
    @56
    @26
    cF
    wceq
    #
    wa
    #
    vn
    @25
    cG
    @44
    @19
    cvv
    @63
    @24
    c1st
    fvexd
    @63
    @25
    @1
    c1st
    cfv
    #
    cG
    @63
    @24
    @1
    c1st
    wph
    @53
    @54
    @62
    simplrr
    #
    fveq2d
    wph
    @64
    cG
    wceq
    #
    @55
    @62
    wph
    cG
    @20
    wcel
    #
    cY
    cB
    wcel
    #
    @66
    evlf2.g
    evlf2.y
    cG
    cY
    @20
    cB
    op1stg
    syl2anc
    ad2antrr
    eqtrd
    @63
    @27
    cG
    wceq
    #
    wa
    #
    va
    vg
    @28
    @31
    @43
    @3
    @4
    @18
    @70
    @26
    cF
    @27
    cG
    cN
    @56
    @62
    @69
    simplr
    #
    @63
    @69
    simpr
    #
    oveq12d
    @70
    @29
    cX
    @30
    cY
    cH
    @70
    @29
    @0
    c2nd
    cfv
    #
    cX
    @70
    @22
    @0
    c2nd
    @56
    @53
    @62
    @69
    @58
    ad2antrr
    fveq2d
    wph
    @73
    cX
    wceq
    #
    @55
    @62
    @69
    wph
    @60
    @61
    @74
    evlf2.f
    evlf2.x
    cF
    cX
    @20
    cB
    op2ndg
    syl2anc
    ad3antrrr
    eqtrd
    #
    @70
    @30
    @1
    c2nd
    cfv
    #
    cY
    @70
    @24
    @1
    c2nd
    @63
    @54
    @69
    @65
    adantr
    fveq2d
    wph
    @76
    cY
    wceq
    #
    @55
    @62
    @69
    wph
    @67
    @68
    @77
    evlf2.g
    evlf2.y
    cG
    cY
    @20
    cB
    op2ndg
    syl2anc
    ad3antrrr
    eqtrd
    #
    oveq12d
    @70
    @32
    @6
    @35
    @10
    @42
    @17
    @70
    @39
    @14
    @41
    @16
    c.x
    @70
    @37
    @12
    @38
    @13
    @70
    @29
    cX
    @36
    @11
    @70
    @26
    cF
    c1st
    @71
    fveq2d
    #
    @75
    fveq12d
    @70
    @30
    cY
    @36
    @11
    @79
    @78
    fveq12d
    opeq12d
    @70
    @30
    cY
    @40
    @15
    @70
    @27
    cG
    c1st
    @72
    fveq2d
    @78
    fveq12d
    oveq12d
    @70
    @30
    cY
    @5
    @78
    fveq2d
    @70
    @7
    @34
    @9
    @70
    @29
    cX
    @30
    cY
    @33
    @8
    @70
    @26
    cF
    c2nd
    @71
    fveq2d
    @75
    @78
    oveq123d
    fveq1d
    oveq123d
    mpt2eq123dv
    csbied2
    csbied2
    wph
    @60
    @61
    @0
    @21
    wcel
    evlf2.f
    evlf2.x
    cF
    cX
    @20
    cB
    opelxpi
    syl2anc
    wph
    @67
    @68
    @1
    @21
    wcel
    evlf2.g
    evlf2.y
    cG
    cY
    @20
    cB
    opelxpi
    syl2anc
    @19
    cvv
    wcel
    wph
    va
    vg
    @3
    @4
    @18
    cF
    cG
    cN
    ovex
    cX
    cY
    cH
    ovex
    mpt2ex
    a1i
    ovmpt2d
    syl5eq
end
