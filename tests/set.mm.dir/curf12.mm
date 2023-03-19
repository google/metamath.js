include "c2nd.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cop.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "wceq.mm"
include "c1st.mm"
include "curf1.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "mpt2ex.mm"
include "op2ndd.mm"
include "syl.mm"
include "wcel.mm"
include "adantr.mm"
include "wa.mm"
include "ovex.mm"
include "a1i.mm"
include "simprl.mm"
include "simprr.mm"
include "oveq12d.mm"
include "eleqtrrd.mm"
include "ovexd.mm"
include "simplrl.mm"
include "opeq2d.mm"
include "simplrr.mm"
include "eqidd.mm"
include "simpr.mm"
include "oveq123d.mm"
include "fvmptdv2.mm"
include "ovmpt2dv.mm"
include "mpd.mm"

theorem curf12
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.1: class .1.
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vh: setvar h
  let vw: setvar w
  let cI: class I
  assume curfval.g: |- G = ( <. C , D >. curryF F )
  assume curfval.a: |- A = ( Base ` C )
  assume curfval.c: |- ( ph -> C e. Cat )
  assume curfval.d: |- ( ph -> D e. Cat )
  assume curfval.f: |- ( ph -> F e. ( ( C Xc. D ) Func E ) )
  assume curfval.b: |- B = ( Base ` D )
  assume curf1.x: |- ( ph -> X e. A )
  assume curf1.k: |- K = ( ( 1st ` G ) ` X )
  assume curf11.y: |- ( ph -> Y e. B )
  assume curf12.j: |- J = ( Hom ` D )
  assume curf12.1: |- .1. = ( Id ` C )
  assume curf12.y: |- ( ph -> Z e. B )
  assume curf12.g: |- ( ph -> H e. ( Y J Z ) )


  assert |- ( ph -> ( ( Y ( 2nd ` K ) Z ) ` H ) = ( ( .1. ` X ) ( <. X , Y >. ( 2nd ` F ) <. X , Z >. ) H ) )

  proof
    wph
    cK
    c2nd
    cfv
    #
    vy
    vz
    cB
    cB
    vg
    vy
    cv
    #
    vz
    cv
    #
    cJ
    co
    #
    cX
    c.1
    cfv
    #
    vg
    cv
    #
    cX
    @1
    cop
    #
    cX
    @2
    cop
    #
    cF
    c2nd
    cfv
    #
    co
    #
    co
    #
    cmpt
    #
    cmpt2
    #
    wceq
    #
    cH
    cY
    cZ
    @0
    co
    #
    cfv
    @4
    cH
    cX
    cY
    cop
    #
    cX
    cZ
    cop
    #
    @8
    co
    #
    co
    #
    wceq
    #
    wph
    cK
    vy
    cB
    cX
    @1
    cF
    c1st
    cfv
    co
    #
    cmpt
    #
    @12
    cop
    wceq
    @13
    wph
    vy
    vz
    cA
    cB
    cC
    cD
    c.1
    vg
    cE
    cF
    cG
    cJ
    cK
    cX
    curfval.g
    curfval.a
    curfval.c
    curfval.d
    curfval.f
    curfval.b
    curf1.x
    curf1.k
    curf12.j
    curf12.1
    curf1
    @21
    @12
    cK
    vy
    cB
    @20
    cB
    cD
    cbs
    cfv
    cvv
    curfval.b
    cD
    cbs
    fvex
    eqeltri
    #
    mptex
    vy
    vz
    cB
    cB
    @11
    @22
    @22
    mpt2ex
    op2ndd
    syl
    wph
    @19
    vy
    vz
    cY
    cZ
    cB
    cB
    @11
    @0
    cvv
    curf11.y
    wph
    cZ
    cB
    wcel
    @1
    cY
    wceq
    #
    curf12.y
    adantr
    @11
    cvv
    wcel
    wph
    @23
    @2
    cZ
    wceq
    #
    wa
    #
    wa
    #
    vg
    @3
    @10
    @1
    @2
    cJ
    ovex
    mptex
    a1i
    @26
    vg
    cH
    @10
    @18
    @3
    @14
    cvv
    @26
    cH
    cY
    cZ
    cJ
    co
    #
    @3
    wph
    cH
    @27
    wcel
    @25
    curf12.g
    adantr
    @26
    @1
    cY
    @2
    cZ
    cJ
    wph
    @23
    @24
    simprl
    wph
    @23
    @24
    simprr
    oveq12d
    eleqtrrd
    @26
    @5
    cH
    wceq
    #
    wa
    #
    @4
    @5
    @9
    ovexd
    @29
    @4
    @4
    @5
    cH
    @9
    @17
    @29
    @6
    @15
    @7
    @16
    @8
    @29
    @1
    cY
    cX
    wph
    @23
    @24
    @28
    simplrl
    opeq2d
    @29
    @2
    cZ
    cX
    wph
    @23
    @24
    @28
    simplrr
    opeq2d
    oveq12d
    @29
    @4
    eqidd
    @26
    @28
    simpr
    oveq123d
    fvmptdv2
    ovmpt2dv
    mpd
end
