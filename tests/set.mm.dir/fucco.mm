include "co.mm"
include "cv.mm"
include "cfv.mm"
include "c1st.mm"
include "cop.mm"
include "cmpt.mm"
include "cvv.mm"
include "cfunc.mm"
include "cxp.mm"
include "c2nd.mm"
include "cmpt2.mm"
include "csb.mm"
include "eqid.mm"
include "ccat.mm"
include "wcel.mm"
include "wa.mm"
include "natrcl.mm"
include "syl.mm"
include "simpld.mm"
include "funcrcl.mm"
include "simprd.mm"
include "fuccofval.mm"
include "wceq.mm"
include "fvexd.mm"
include "simprl.mm"
include "fveq2d.mm"
include "op1stg.mm"
include "adantr.mm"
include "eqtrd.mm"
include "op2ndg.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "simprr.mm"
include "oveq12d.mm"
include "simplr.mm"
include "fveq1d.mm"
include "opeq12d.mm"
include "oveqd.mm"
include "mpteq2dv.mm"
include "mpt2eq123dv.mm"
include "csbied2.mm"
include "opelxpi.mm"
include "ovex.mm"
include "mpt2ex.mm"
include "a1i.mm"
include "ovmpt2d.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"

theorem fucco
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cH: class H
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vv: setvar v
  let cX: class X
  assume fucco.q: |- Q = ( C FuncCat D )
  assume fucco.n: |- N = ( C Nat D )
  assume fucco.a: |- A = ( Base ` C )
  assume fucco.o: |- .x. = ( comp ` D )
  assume fucco.x: |- .xb = ( comp ` Q )
  assume fucco.f: |- ( ph -> R e. ( F N G ) )
  assume fucco.g: |- ( ph -> S e. ( G N H ) )

  disjoint A x
  disjoint ph x
  disjoint R x
  disjoint S x
  disjoint C x
  disjoint D x
  disjoint .x. x
  disjoint F x
  disjoint G x
  disjoint H x
  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a v
  disjoint a x
  disjoint A a
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b v
  disjoint b x
  disjoint A b
  disjoint f g
  disjoint f h
  disjoint f v
  disjoint f x
  disjoint A f
  disjoint g h
  disjoint g v
  disjoint g x
  disjoint A g
  disjoint h v
  disjoint h x
  disjoint A h
  disjoint v x
  disjoint A v
  disjoint a ph
  disjoint b ph
  disjoint f ph
  disjoint g ph
  disjoint h ph
  disjoint ph v
  disjoint R a
  disjoint R b
  disjoint S a
  disjoint S b
  disjoint C a
  disjoint C b
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint C v
  disjoint D a
  disjoint D b
  disjoint D f
  disjoint D g
  disjoint D h
  disjoint D v
  disjoint .x. a
  disjoint .x. b
  disjoint .x. f
  disjoint .x. g
  disjoint .x. h
  disjoint .x. v
  disjoint F a
  disjoint F b
  disjoint F f
  disjoint F g
  disjoint F h
  disjoint F v
  disjoint G a
  disjoint G b
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint G v
  disjoint H a
  disjoint H b
  disjoint H f
  disjoint H g
  disjoint H h
  disjoint H v
  disjoint N a
  disjoint N b
  disjoint N f
  disjoint N g
  disjoint N h
  disjoint N v
  disjoint X x
  assert |- ( ph -> ( S ( <. F , G >. .xb H ) R ) = ( x e. A |-> ( ( S ` x ) ( <. ( ( 1st ` F ) ` x ) , ( ( 1st ` G ) ` x ) >. .x. ( ( 1st ` H ) ` x ) ) ( R ` x ) ) ) )

  proof
    wph
    vb
    va
    cS
    cR
    cG
    cH
    cN
    co
    #
    cF
    cG
    cN
    co
    #
    vx
    cA
    vx
    cv
    #
    vb
    cv
    #
    cfv
    #
    @2
    va
    cv
    #
    cfv
    #
    @2
    cF
    c1st
    cfv
    #
    cfv
    #
    @2
    cG
    c1st
    cfv
    #
    cfv
    #
    cop
    #
    @2
    cH
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
    cmpt
    #
    vx
    cA
    @2
    cS
    cfv
    #
    @2
    cR
    cfv
    #
    @14
    co
    #
    cmpt
    #
    cF
    cG
    cop
    #
    cH
    c.xb
    co
    cvv
    wph
    vv
    vh
    @21
    cH
    cC
    cD
    cfunc
    co
    #
    @22
    cxp
    #
    @22
    vf
    vv
    cv
    #
    c1st
    cfv
    #
    vg
    @24
    c2nd
    cfv
    #
    vb
    va
    vg
    cv
    #
    vh
    cv
    #
    cN
    co
    #
    vf
    cv
    #
    @27
    cN
    co
    #
    vx
    cA
    @4
    @6
    @2
    @30
    c1st
    cfv
    #
    cfv
    #
    @2
    @27
    c1st
    cfv
    #
    cfv
    #
    cop
    #
    @2
    @28
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
    cmpt
    #
    cmpt2
    #
    csb
    #
    csb
    vb
    va
    @0
    @1
    @16
    cmpt2
    #
    c.xb
    cvv
    wph
    vx
    vv
    cA
    @22
    cC
    cD
    cQ
    c.xb
    c.x
    vf
    vg
    vh
    cN
    va
    vb
    fucco.q
    @22
    eqid
    fucco.n
    fucco.a
    fucco.o
    wph
    cC
    ccat
    wcel
    #
    cD
    ccat
    wcel
    #
    wph
    cF
    @22
    wcel
    #
    @45
    @46
    wa
    wph
    @47
    cG
    @22
    wcel
    #
    wph
    cR
    @1
    wcel
    @47
    @48
    wa
    #
    fucco.f
    cR
    cC
    cD
    cF
    cG
    cN
    fucco.n
    natrcl
    syl
    #
    simpld
    cC
    cD
    cF
    funcrcl
    syl
    #
    simpld
    wph
    @45
    @46
    @51
    simprd
    fucco.x
    fuccofval
    wph
    @24
    @21
    wceq
    #
    @28
    cH
    wceq
    #
    wa
    #
    wa
    #
    vf
    @25
    cF
    @43
    @44
    cvv
    @55
    @24
    c1st
    fvexd
    @55
    @25
    @21
    c1st
    cfv
    #
    cF
    @55
    @24
    @21
    c1st
    wph
    @52
    @53
    simprl
    #
    fveq2d
    wph
    @56
    cF
    wceq
    #
    @54
    wph
    @49
    @58
    @50
    cF
    cG
    @22
    @22
    op1stg
    syl
    adantr
    eqtrd
    @55
    @30
    cF
    wceq
    #
    wa
    #
    vg
    @26
    cG
    @42
    @44
    cvv
    @60
    @24
    c2nd
    fvexd
    @60
    @26
    @21
    c2nd
    cfv
    #
    cG
    @60
    @24
    @21
    c2nd
    @55
    @52
    @59
    @57
    adantr
    fveq2d
    wph
    @61
    cG
    wceq
    #
    @54
    @59
    wph
    @49
    @62
    @50
    cF
    cG
    @22
    @22
    op2ndg
    syl
    ad2antrr
    eqtrd
    @60
    @27
    cG
    wceq
    #
    wa
    #
    vb
    va
    @29
    @31
    @41
    @0
    @1
    @16
    @64
    @27
    cG
    @28
    cH
    cN
    @60
    @63
    simpr
    #
    @55
    @53
    @59
    @63
    wph
    @52
    @53
    simprr
    ad2antrr
    #
    oveq12d
    @64
    @30
    cF
    @27
    cG
    cN
    @55
    @59
    @63
    simplr
    #
    @65
    oveq12d
    @64
    vx
    cA
    @40
    @15
    @64
    @39
    @14
    @4
    @6
    @64
    @36
    @11
    @38
    @13
    c.x
    @64
    @33
    @8
    @35
    @10
    @64
    @2
    @32
    @7
    @64
    @30
    cF
    c1st
    @67
    fveq2d
    fveq1d
    @64
    @2
    @34
    @9
    @64
    @27
    cG
    c1st
    @65
    fveq2d
    fveq1d
    opeq12d
    @64
    @2
    @37
    @12
    @64
    @28
    cH
    c1st
    @66
    fveq2d
    fveq1d
    oveq12d
    oveqd
    mpteq2dv
    mpt2eq123dv
    csbied2
    csbied2
    wph
    @49
    @21
    @23
    wcel
    @50
    cF
    cG
    @22
    @22
    opelxpi
    syl
    wph
    @48
    cH
    @22
    wcel
    #
    wph
    cS
    @0
    wcel
    @48
    @68
    wa
    fucco.g
    cS
    cC
    cD
    cG
    cH
    cN
    fucco.n
    natrcl
    syl
    simprd
    @44
    cvv
    wcel
    wph
    vb
    va
    @0
    @1
    @16
    cG
    cH
    cN
    ovex
    cF
    cG
    cN
    ovex
    mpt2ex
    a1i
    ovmpt2d
    wph
    @3
    cS
    wceq
    #
    @5
    cR
    wceq
    #
    wa
    wa
    #
    vx
    cA
    @15
    @19
    @71
    @4
    @17
    @6
    @18
    @14
    @71
    @2
    @3
    cS
    wph
    @69
    @70
    simprl
    fveq1d
    @71
    @2
    @5
    cR
    wph
    @69
    @70
    simprr
    fveq1d
    oveq12d
    mpteq2dv
    fucco.g
    fucco.f
    @20
    cvv
    wcel
    wph
    vx
    cA
    @19
    cA
    cC
    cbs
    cfv
    cvv
    fucco.a
    cC
    cbs
    fvex
    eqeltri
    mptex
    a1i
    ovmpt2d
end
