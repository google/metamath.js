include "cxp.mm"
include "cv.mm"
include "c2nd.mm"
include "cfv.mm"
include "co.mm"
include "c1st.mm"
include "cop.mm"
include "cmpt2.mm"
include "wceq.mm"
include "xpccofval.mm"
include "cvv.mm"
include "wcel.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "adantr.mm"
include "wa.mm"
include "ovex.mm"
include "fvex.mm"
include "mpt2ex.mm"
include "a1i.mm"
include "simprl.mm"
include "fveq2d.mm"
include "op2ndg.mm"
include "eqtrd.mm"
include "simprr.mm"
include "oveq12d.mm"
include "eleqtrrd.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "opex.mm"
include "op1stg.mm"
include "opeq12d.mm"
include "simplrr.mm"
include "oveq123d.mm"
include "ovmpt2dv2.mm"
include "ovmpt2dv.mm"
include "mpi.mm"

theorem xpcco
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let c.xb: class .xb
  let cT: class T
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cK: class K
  let cO: class O
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vf: setvar f
  let vg: setvar g
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  assume xpccofval.t: |- T = ( C Xc. D )
  assume xpccofval.b: |- B = ( Base ` T )
  assume xpccofval.k: |- K = ( Hom ` T )
  assume xpccofval.o1: |- .x. = ( comp ` C )
  assume xpccofval.o2: |- .xb = ( comp ` D )
  assume xpccofval.o: |- O = ( comp ` T )
  assume xpcco.x: |- ( ph -> X e. B )
  assume xpcco.y: |- ( ph -> Y e. B )
  assume xpcco.z: |- ( ph -> Z e. B )
  assume xpcco.f: |- ( ph -> F e. ( X K Y ) )
  assume xpcco.g: |- ( ph -> G e. ( Y K Z ) )


  assert |- ( ph -> ( G ( <. X , Y >. O Z ) F ) = <. ( ( 1st ` G ) ( <. ( 1st ` X ) , ( 1st ` Y ) >. .x. ( 1st ` Z ) ) ( 1st ` F ) ) , ( ( 2nd ` G ) ( <. ( 2nd ` X ) , ( 2nd ` Y ) >. .xb ( 2nd ` Z ) ) ( 2nd ` F ) ) >. )

  proof
    wph
    cO
    vx
    vy
    cB
    cB
    cxp
    #
    cB
    vg
    vf
    vx
    cv
    #
    c2nd
    cfv
    #
    vy
    cv
    #
    cK
    co
    #
    @1
    cK
    cfv
    #
    vg
    cv
    #
    c1st
    cfv
    #
    vf
    cv
    #
    c1st
    cfv
    #
    @1
    c1st
    cfv
    #
    c1st
    cfv
    #
    @2
    c1st
    cfv
    #
    cop
    #
    @3
    c1st
    cfv
    #
    c.x
    co
    #
    co
    #
    @6
    c2nd
    cfv
    #
    @8
    c2nd
    cfv
    #
    @10
    c2nd
    cfv
    #
    @2
    c2nd
    cfv
    #
    cop
    #
    @3
    c2nd
    cfv
    #
    c.xb
    co
    #
    co
    #
    cop
    #
    cmpt2
    #
    cmpt2
    wceq
    cG
    cF
    cX
    cY
    cop
    #
    cZ
    cO
    co
    #
    co
    cG
    c1st
    cfv
    #
    cF
    c1st
    cfv
    #
    cX
    c1st
    cfv
    #
    cY
    c1st
    cfv
    #
    cop
    #
    cZ
    c1st
    cfv
    #
    c.x
    co
    #
    co
    #
    cG
    c2nd
    cfv
    #
    cF
    c2nd
    cfv
    #
    cX
    c2nd
    cfv
    #
    cY
    c2nd
    cfv
    #
    cop
    #
    cZ
    c2nd
    cfv
    #
    c.xb
    co
    #
    co
    #
    cop
    #
    wceq
    #
    vx
    vy
    cB
    cC
    cD
    c.xb
    cT
    c.x
    vf
    vg
    cK
    cO
    xpccofval.t
    xpccofval.b
    xpccofval.k
    xpccofval.o1
    xpccofval.o2
    xpccofval.o
    xpccofval
    wph
    @46
    vx
    vy
    @27
    cZ
    @0
    cB
    @26
    cO
    cvv
    wph
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    @27
    @0
    wcel
    xpcco.x
    xpcco.y
    cX
    cY
    cB
    cB
    opelxpi
    syl2anc
    wph
    cZ
    cB
    wcel
    @1
    @27
    wceq
    #
    xpcco.z
    adantr
    @26
    cvv
    wcel
    wph
    @49
    @3
    cZ
    wceq
    #
    wa
    #
    wa
    #
    vg
    vf
    @4
    @5
    @25
    @2
    @3
    cK
    ovex
    @1
    cK
    fvex
    mpt2ex
    a1i
    @52
    vg
    vf
    cG
    cF
    @4
    @5
    @25
    @45
    @28
    cvv
    @52
    cG
    cY
    cZ
    cK
    co
    #
    @4
    wph
    cG
    @53
    wcel
    @51
    xpcco.g
    adantr
    @52
    @2
    cY
    @3
    cZ
    cK
    @52
    @2
    @27
    c2nd
    cfv
    #
    cY
    @52
    @1
    @27
    c2nd
    wph
    @49
    @50
    simprl
    #
    fveq2d
    wph
    @54
    cY
    wceq
    #
    @51
    wph
    @47
    @48
    @56
    xpcco.x
    xpcco.y
    cX
    cY
    cB
    cB
    op2ndg
    syl2anc
    adantr
    eqtrd
    #
    wph
    @49
    @50
    simprr
    oveq12d
    eleqtrrd
    @52
    cF
    @5
    wcel
    @6
    cG
    wceq
    #
    @52
    cF
    cX
    cY
    cK
    co
    #
    @5
    wph
    cF
    @59
    wcel
    @51
    xpcco.f
    adantr
    @52
    @5
    @27
    cK
    cfv
    @59
    @52
    @1
    @27
    cK
    @55
    fveq2d
    cX
    cY
    cK
    df-ov
    syl6eqr
    eleqtrrd
    adantr
    @25
    cvv
    wcel
    @52
    @58
    @8
    cF
    wceq
    #
    wa
    #
    wa
    #
    @16
    @24
    opex
    a1i
    @62
    @16
    @36
    @24
    @44
    @62
    @7
    @29
    @9
    @30
    @15
    @35
    @62
    @13
    @33
    @14
    @34
    c.x
    @62
    @11
    @31
    @12
    @32
    @62
    @10
    cX
    c1st
    @52
    @10
    cX
    wceq
    @61
    @52
    @10
    @27
    c1st
    cfv
    #
    cX
    @52
    @1
    @27
    c1st
    @55
    fveq2d
    wph
    @63
    cX
    wceq
    #
    @51
    wph
    @47
    @48
    @64
    xpcco.x
    xpcco.y
    cX
    cY
    cB
    cB
    op1stg
    syl2anc
    adantr
    eqtrd
    adantr
    #
    fveq2d
    @62
    @2
    cY
    c1st
    @52
    @2
    cY
    wceq
    @61
    @57
    adantr
    #
    fveq2d
    opeq12d
    @62
    @3
    cZ
    c1st
    wph
    @49
    @50
    @61
    simplrr
    #
    fveq2d
    oveq12d
    @62
    @6
    cG
    c1st
    @52
    @58
    @60
    simprl
    #
    fveq2d
    @62
    @8
    cF
    c1st
    @52
    @58
    @60
    simprr
    #
    fveq2d
    oveq123d
    @62
    @17
    @37
    @18
    @38
    @23
    @43
    @62
    @21
    @41
    @22
    @42
    c.xb
    @62
    @19
    @39
    @20
    @40
    @62
    @10
    cX
    c2nd
    @65
    fveq2d
    @62
    @2
    cY
    c2nd
    @66
    fveq2d
    opeq12d
    @62
    @3
    cZ
    c2nd
    @67
    fveq2d
    oveq12d
    @62
    @6
    cG
    c2nd
    @68
    fveq2d
    @62
    @8
    cF
    c2nd
    @69
    fveq2d
    oveq123d
    opeq12d
    ovmpt2dv2
    ovmpt2dv
    mpi
end
