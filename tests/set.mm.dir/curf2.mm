include "c2nd.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "cop.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "wceq.mm"
include "c1st.mm"
include "chom.mm"
include "ccid.mm"
include "eqid.mm"
include "curfval.mm"
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
include "simplrl.mm"
include "opeq1d.mm"
include "simplrr.mm"
include "simpr.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "mpteq2dv.mm"
include "fvmptdv2.mm"
include "ovmpt2dv.mm"
include "mpd.mm"
include "syl5eq.mm"

theorem curf2
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vg: setvar g
  let vf: setvar f
  let vw: setvar w
  let cZ: class Z
  assume curf2.g: |- G = ( <. C , D >. curryF F )
  assume curf2.a: |- A = ( Base ` C )
  assume curf2.c: |- ( ph -> C e. Cat )
  assume curf2.d: |- ( ph -> D e. Cat )
  assume curf2.f: |- ( ph -> F e. ( ( C Xc. D ) Func E ) )
  assume curf2.b: |- B = ( Base ` D )
  assume curf2.h: |- H = ( Hom ` C )
  assume curf2.i: |- I = ( Id ` D )
  assume curf2.x: |- ( ph -> X e. A )
  assume curf2.y: |- ( ph -> Y e. A )
  assume curf2.k: |- ( ph -> K e. ( X H Y ) )
  assume curf2.l: |- L = ( ( X ( 2nd ` G ) Y ) ` K )

  disjoint C z
  disjoint F z
  disjoint H z
  disjoint L z
  disjoint E z
  disjoint G z
  disjoint I z
  disjoint ph z
  disjoint B z
  disjoint D z
  disjoint X z
  disjoint K z
  disjoint Y z
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint C g
  disjoint x z
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint F g
  disjoint F x
  disjoint F y
  disjoint H g
  disjoint H y
  disjoint f w
  disjoint f z
  disjoint L f
  disjoint w z
  disjoint L w
  disjoint f g
  disjoint f y
  disjoint E f
  disjoint g w
  disjoint E g
  disjoint w y
  disjoint E w
  disjoint E y
  disjoint f x
  disjoint G f
  disjoint w x
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint I g
  disjoint I x
  disjoint I y
  disjoint f ph
  disjoint g ph
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint B f
  disjoint B g
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint D f
  disjoint D g
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint X f
  disjoint X g
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint Z z
  disjoint K g
  disjoint K x
  disjoint K y
  disjoint Y f
  disjoint Y g
  disjoint Y w
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> L = ( z e. B |-> ( K ( <. X , z >. ( 2nd ` F ) <. Y , z >. ) ( I ` z ) ) ) )

  proof
    wph
    cL
    cK
    cX
    cY
    cG
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    vz
    cB
    cK
    vz
    cv
    #
    cI
    cfv
    #
    cX
    @3
    cop
    #
    cY
    @3
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
    curf2.l
    wph
    @0
    vx
    vy
    cA
    cA
    vg
    vx
    cv
    #
    vy
    cv
    #
    cH
    co
    #
    vz
    cB
    vg
    cv
    #
    @4
    @11
    @3
    cop
    #
    @12
    @3
    cop
    #
    @7
    co
    #
    co
    #
    cmpt
    #
    cmpt
    #
    cmpt2
    #
    wceq
    #
    @2
    @10
    wceq
    #
    wph
    cG
    vx
    cA
    vy
    cB
    @11
    @12
    cF
    c1st
    cfv
    co
    cmpt
    vy
    vz
    cB
    cB
    vg
    @12
    @3
    cD
    chom
    cfv
    #
    co
    @11
    cC
    ccid
    cfv
    #
    cfv
    @14
    @11
    @12
    cop
    @15
    @7
    co
    co
    cmpt
    cmpt2
    cop
    #
    cmpt
    #
    @21
    cop
    wceq
    @22
    wph
    vx
    vy
    vz
    cA
    cB
    cC
    cD
    @25
    vg
    cE
    cF
    cG
    cH
    cI
    @24
    curf2.g
    curf2.a
    curf2.c
    curf2.d
    curf2.f
    curf2.b
    @24
    eqid
    @25
    eqid
    curf2.h
    curf2.i
    curfval
    @27
    @21
    cG
    vx
    cA
    @26
    cA
    cC
    cbs
    cfv
    cvv
    curf2.a
    cC
    cbs
    fvex
    eqeltri
    #
    mptex
    vx
    vy
    cA
    cA
    @20
    @28
    @28
    mpt2ex
    op2ndd
    syl
    wph
    @23
    vx
    vy
    cX
    cY
    cA
    cA
    @20
    @0
    cvv
    curf2.x
    wph
    cY
    cA
    wcel
    @11
    cX
    wceq
    #
    curf2.y
    adantr
    @20
    cvv
    wcel
    wph
    @29
    @12
    cY
    wceq
    #
    wa
    #
    wa
    #
    vg
    @13
    @19
    @11
    @12
    cH
    ovex
    mptex
    a1i
    @32
    vg
    cK
    @19
    @10
    @13
    @1
    cvv
    @32
    cK
    cX
    cY
    cH
    co
    #
    @13
    wph
    cK
    @33
    wcel
    @31
    curf2.k
    adantr
    @32
    @11
    cX
    @12
    cY
    cH
    wph
    @29
    @30
    simprl
    wph
    @29
    @30
    simprr
    oveq12d
    eleqtrrd
    @19
    cvv
    wcel
    @32
    @14
    cK
    wceq
    #
    wa
    #
    vz
    cB
    @18
    cB
    cD
    cbs
    cfv
    cvv
    curf2.b
    cD
    cbs
    fvex
    eqeltri
    mptex
    a1i
    @35
    vz
    cB
    @18
    @9
    @35
    @14
    cK
    @4
    @4
    @17
    @8
    @35
    @15
    @5
    @16
    @6
    @7
    @35
    @11
    cX
    @3
    wph
    @29
    @30
    @34
    simplrl
    opeq1d
    @35
    @12
    cY
    @3
    wph
    @29
    @30
    @34
    simplrr
    opeq1d
    oveq12d
    @32
    @34
    simpr
    @35
    @4
    eqidd
    oveq123d
    mpteq2dv
    fvmptdv2
    ovmpt2dv
    mpd
    syl5eq
end
