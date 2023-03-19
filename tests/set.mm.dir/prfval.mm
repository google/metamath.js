include "cprf.mm"
include "co.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "cop.mm"
include "cmpt.mm"
include "c2nd.mm"
include "cmpt2.mm"
include "cvv.mm"
include "cdm.mm"
include "csb.mm"
include "wceq.mm"
include "df-prf.mm"
include "a1i.mm"
include "wa.mm"
include "wcel.mm"
include "fvex.mm"
include "dmex.mm"
include "simprl.mm"
include "fveq2d.mm"
include "dmeqd.mm"
include "cbs.mm"
include "wf.mm"
include "eqid.mm"
include "cfunc.mm"
include "wrel.mm"
include "wbr.mm"
include "relfunc.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "funcf1.mm"
include "fdm.mm"
include "syl.mm"
include "adantr.mm"
include "eqtrd.mm"
include "simpr.mm"
include "simplrl.mm"
include "fveq1d.mm"
include "simplrr.mm"
include "opeq12d.mm"
include "mpteq12dv.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "ad2antrr.mm"
include "oveqd.mm"
include "chom.mm"
include "ad4antr.mm"
include "simplr.mm"
include "funcf2.mm"
include "3impa.mm"
include "mpt2eq3dva.mm"
include "csbied2.mm"
include "elex.mm"
include "opex.mm"
include "ovmpt2d.mm"
include "syl5eq.mm"

theorem prfval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let vh: setvar h
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let cK: class K
  let cX: class X
  let cY: class Y
  assume prfval.k: |- P = ( F pairF G )
  assume prfval.b: |- B = ( Base ` C )
  assume prfval.h: |- H = ( Hom ` C )
  assume prfval.c: |- ( ph -> F e. ( C Func D ) )
  assume prfval.d: |- ( ph -> G e. ( C Func E ) )

  disjoint h x
  disjoint h y
  disjoint B h
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint F h
  disjoint F x
  disjoint F y
  disjoint h ph
  disjoint ph x
  disjoint ph y
  disjoint D x
  disjoint D y
  disjoint G h
  disjoint G x
  disjoint G y
  disjoint H h
  disjoint H x
  disjoint H y
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint f g
  disjoint f h
  disjoint f x
  disjoint f y
  disjoint B f
  disjoint g h
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint F b
  disjoint F f
  disjoint F g
  disjoint b ph
  disjoint f ph
  disjoint g ph
  disjoint G b
  disjoint G f
  disjoint G g
  disjoint K h
  disjoint X h
  disjoint X x
  disjoint X y
  disjoint Y h
  disjoint Y x
  disjoint Y y
  disjoint H b
  disjoint H f
  disjoint H g
  assert |- ( ph -> P = <. ( x e. B |-> <. ( ( 1st ` F ) ` x ) , ( ( 1st ` G ) ` x ) >. ) , ( x e. B , y e. B |-> ( h e. ( x H y ) |-> <. ( ( x ( 2nd ` F ) y ) ` h ) , ( ( x ( 2nd ` G ) y ) ` h ) >. ) ) >. )

  proof
    wph
    cP
    cF
    cG
    cprf
    co
    vx
    cB
    vx
    cv
    #
    cF
    c1st
    cfv
    #
    cfv
    #
    @0
    cG
    c1st
    cfv
    #
    cfv
    #
    cop
    #
    cmpt
    #
    vx
    vy
    cB
    cB
    vh
    @0
    vy
    cv
    #
    cH
    co
    #
    vh
    cv
    #
    @0
    @7
    cF
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    @9
    @0
    @7
    cG
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    cop
    #
    cmpt
    #
    cmpt2
    #
    cop
    #
    prfval.k
    wph
    vf
    vg
    cF
    cG
    cvv
    cvv
    vb
    vf
    cv
    #
    c1st
    cfv
    #
    cdm
    #
    vx
    vb
    cv
    #
    @0
    @21
    cfv
    #
    @0
    vg
    cv
    #
    c1st
    cfv
    #
    cfv
    #
    cop
    #
    cmpt
    #
    vx
    vy
    @23
    @23
    vh
    @0
    @7
    @20
    c2nd
    cfv
    #
    co
    #
    cdm
    #
    @9
    @31
    cfv
    #
    @9
    @0
    @7
    @25
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    cop
    #
    cmpt
    #
    cmpt2
    #
    cop
    #
    csb
    #
    @19
    cprf
    cvv
    cprf
    vf
    vg
    cvv
    cvv
    @41
    cmpt2
    wceq
    wph
    vx
    vy
    vf
    vg
    vh
    vb
    df-prf
    a1i
    wph
    @20
    cF
    wceq
    #
    @25
    cG
    wceq
    #
    wa
    #
    wa
    #
    vb
    @22
    cB
    @40
    @19
    cvv
    @22
    cvv
    wcel
    @45
    @21
    @20
    c1st
    fvex
    dmex
    a1i
    @45
    @22
    @1
    cdm
    #
    cB
    @45
    @21
    @1
    @45
    @20
    cF
    c1st
    wph
    @42
    @43
    simprl
    fveq2d
    dmeqd
    wph
    @46
    cB
    wceq
    #
    @44
    wph
    cB
    cD
    cbs
    cfv
    #
    @1
    wf
    @47
    wph
    cB
    @48
    cC
    cD
    @1
    @10
    prfval.b
    @48
    eqid
    wph
    cC
    cD
    cfunc
    co
    #
    wrel
    cF
    @49
    wcel
    #
    @1
    @10
    @49
    wbr
    #
    cC
    cD
    relfunc
    prfval.c
    cF
    @49
    1st2ndbr
    sylancr
    #
    funcf1
    cB
    @48
    @1
    fdm
    syl
    adantr
    eqtrd
    @45
    @23
    cB
    wceq
    #
    wa
    #
    @29
    @6
    @39
    @18
    @54
    vx
    @23
    @28
    cB
    @5
    @45
    @53
    simpr
    #
    @54
    @24
    @2
    @27
    @4
    @54
    @0
    @21
    @1
    @54
    @20
    cF
    c1st
    wph
    @42
    @43
    @53
    simplrl
    #
    fveq2d
    fveq1d
    @54
    @0
    @26
    @3
    @54
    @25
    cG
    c1st
    wph
    @42
    @43
    @53
    simplrr
    #
    fveq2d
    fveq1d
    opeq12d
    mpteq12dv
    @54
    @39
    vx
    vy
    cB
    cB
    @38
    cmpt2
    @18
    @54
    vx
    vy
    @23
    @23
    @38
    cB
    cB
    @38
    @55
    @55
    @54
    @38
    eqidd
    mpt2eq123dv
    @54
    vx
    vy
    cB
    cB
    @38
    @17
    @54
    @0
    cB
    wcel
    #
    @7
    cB
    wcel
    #
    @38
    @17
    wceq
    @54
    @58
    wa
    #
    @59
    wa
    #
    vh
    @32
    @37
    @8
    @16
    @61
    @32
    @11
    cdm
    #
    @8
    @61
    @31
    @11
    @61
    @30
    @10
    @0
    @7
    @61
    @20
    cF
    c2nd
    @54
    @42
    @58
    @59
    @56
    ad2antrr
    fveq2d
    oveqd
    #
    dmeqd
    @61
    @8
    @2
    @7
    @1
    cfv
    cD
    chom
    cfv
    #
    co
    #
    @11
    wf
    @62
    @8
    wceq
    @61
    cB
    cC
    cD
    @1
    @10
    cH
    @64
    @0
    @7
    prfval.b
    prfval.h
    @64
    eqid
    wph
    @51
    @44
    @53
    @58
    @59
    @52
    ad4antr
    @54
    @58
    @59
    simplr
    @60
    @59
    simpr
    funcf2
    @8
    @65
    @11
    fdm
    syl
    eqtrd
    @61
    @33
    @12
    @36
    @15
    @61
    @9
    @31
    @11
    @63
    fveq1d
    @61
    @9
    @35
    @14
    @61
    @34
    @13
    @0
    @7
    @61
    @25
    cG
    c2nd
    @54
    @43
    @58
    @59
    @57
    ad2antrr
    fveq2d
    oveqd
    fveq1d
    opeq12d
    mpteq12dv
    3impa
    mpt2eq3dva
    eqtrd
    opeq12d
    csbied2
    wph
    @50
    cF
    cvv
    wcel
    prfval.c
    cF
    @49
    elex
    syl
    wph
    cG
    cC
    cE
    cfunc
    co
    #
    wcel
    cG
    cvv
    wcel
    prfval.d
    cG
    @66
    elex
    syl
    @19
    cvv
    wcel
    wph
    @6
    @18
    opex
    a1i
    ovmpt2d
    syl5eq
end
