include "cvv.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "ccom.mm"
include "c2nd.mm"
include "cdm.mm"
include "co.mm"
include "cmpt2.mm"
include "cop.mm"
include "ccofu.mm"
include "wceq.mm"
include "df-cofu.mm"
include "a1i.mm"
include "wa.mm"
include "simprl.mm"
include "fveq2d.mm"
include "simprr.mm"
include "coeq12d.mm"
include "cxp.mm"
include "dmeqd.mm"
include "wfn.mm"
include "cfunc.mm"
include "wrel.mm"
include "wcel.mm"
include "wbr.mm"
include "relfunc.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "funcfn2.mm"
include "fndm.mm"
include "syl.mm"
include "adantr.mm"
include "eqtrd.mm"
include "dmxpid.mm"
include "syl6eq.mm"
include "fveq1d.mm"
include "oveq123d.mm"
include "oveqd.mm"
include "mpt2eq123dv.mm"
include "opeq12d.mm"
include "elex.mm"
include "opex.mm"
include "ovmpt2d.mm"

theorem cofuval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let cX: class X
  let cY: class Y
  assume cofuval.b: |- B = ( Base ` C )
  assume cofuval.f: |- ( ph -> F e. ( C Func D ) )
  assume cofuval.g: |- ( ph -> G e. ( D Func E ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint ph x
  disjoint ph y
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint B f
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint F f
  disjoint F g
  disjoint G f
  disjoint G g
  disjoint f ph
  disjoint g ph
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> ( G o.func F ) = <. ( ( 1st ` G ) o. ( 1st ` F ) ) , ( x e. B , y e. B |-> ( ( ( ( 1st ` F ) ` x ) ( 2nd ` G ) ( ( 1st ` F ) ` y ) ) o. ( x ( 2nd ` F ) y ) ) ) >. )

  proof
    wph
    vg
    vf
    cG
    cF
    cvv
    cvv
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
    ccom
    #
    vx
    vy
    @2
    c2nd
    cfv
    #
    cdm
    #
    cdm
    #
    @7
    vx
    cv
    #
    @3
    cfv
    #
    vy
    cv
    #
    @3
    cfv
    #
    @0
    c2nd
    cfv
    #
    co
    #
    @8
    @10
    @5
    co
    #
    ccom
    #
    cmpt2
    #
    cop
    #
    cG
    c1st
    cfv
    #
    cF
    c1st
    cfv
    #
    ccom
    #
    vx
    vy
    cB
    cB
    @8
    @19
    cfv
    #
    @10
    @19
    cfv
    #
    cG
    c2nd
    cfv
    #
    co
    #
    @8
    @10
    cF
    c2nd
    cfv
    #
    co
    #
    ccom
    #
    cmpt2
    #
    cop
    #
    ccofu
    cvv
    ccofu
    vg
    vf
    cvv
    cvv
    @17
    cmpt2
    wceq
    wph
    vx
    vy
    vf
    vg
    df-cofu
    a1i
    wph
    @0
    cG
    wceq
    #
    @2
    cF
    wceq
    #
    wa
    #
    wa
    #
    @4
    @20
    @16
    @28
    @33
    @1
    @18
    @3
    @19
    @33
    @0
    cG
    c1st
    wph
    @30
    @31
    simprl
    #
    fveq2d
    @33
    @2
    cF
    c1st
    wph
    @30
    @31
    simprr
    #
    fveq2d
    #
    coeq12d
    @33
    vx
    vy
    @7
    @7
    @15
    cB
    cB
    @27
    @33
    @7
    cB
    cB
    cxp
    #
    cdm
    cB
    @33
    @6
    @37
    @33
    @6
    @25
    cdm
    #
    @37
    @33
    @5
    @25
    @33
    @2
    cF
    c2nd
    @35
    fveq2d
    #
    dmeqd
    wph
    @38
    @37
    wceq
    #
    @32
    wph
    @25
    @37
    wfn
    @40
    wph
    cB
    cC
    cD
    @19
    @25
    cofuval.b
    wph
    cC
    cD
    cfunc
    co
    #
    wrel
    cF
    @41
    wcel
    #
    @19
    @25
    @41
    wbr
    cC
    cD
    relfunc
    cofuval.f
    cF
    @41
    1st2ndbr
    sylancr
    funcfn2
    @37
    @25
    fndm
    syl
    adantr
    eqtrd
    dmeqd
    cB
    dmxpid
    syl6eq
    #
    @43
    @33
    @13
    @24
    @14
    @26
    @33
    @9
    @21
    @11
    @22
    @12
    @23
    @33
    @0
    cG
    c2nd
    @34
    fveq2d
    @33
    @8
    @3
    @19
    @36
    fveq1d
    @33
    @10
    @3
    @19
    @36
    fveq1d
    oveq123d
    @33
    @5
    @25
    @8
    @10
    @39
    oveqd
    coeq12d
    mpt2eq123dv
    opeq12d
    wph
    cG
    cD
    cE
    cfunc
    co
    #
    wcel
    cG
    cvv
    wcel
    cofuval.g
    cG
    @44
    elex
    syl
    wph
    @42
    cF
    cvv
    wcel
    cofuval.f
    cF
    @41
    elex
    syl
    @29
    cvv
    wcel
    wph
    @20
    @28
    opex
    a1i
    ovmpt2d
end
