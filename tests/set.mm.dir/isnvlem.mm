include "cop.mm"
include "cnv.mm"
include "wcel.mm"
include "cv.mm"
include "cvc.mm"
include "crn.mm"
include "cr.mm"
include "wf.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cgi.mm"
include "wi.mm"
include "co.mm"
include "cabs.mm"
include "cmul.mm"
include "cc.mm"
include "wral.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "coprab.mm"
include "cvv.mm"
include "df-nv.mm"
include "eleq2i.mm"
include "opeq1.mm"
include "eleq1d.mm"
include "rneq.mm"
include "syl6eqr.mm"
include "feq2d.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "imbi2d.mm"
include "oveq.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "raleqbidv.mm"
include "3anbi13d.mm"
include "3anbi123d.mm"
include "opeq2.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "3anbi2d.mm"
include "feq1.mm"
include "fveq1.mm"
include "imbi1d.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "oveq12d.mm"
include "breq12d.mm"
include "3anbi23d.mm"
include "eloprabg.mm"
include "syl5bb.mm"

theorem isnvlem
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cG: class G
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vg: setvar g
  let vn: setvar n
  let vs: setvar s
  assume isnvlem.1: |- X = ran G
  assume isnvlem.2: |- Z = ( GId ` G )

  disjoint x y
  disjoint G x
  disjoint G y
  disjoint N x
  disjoint N y
  disjoint S x
  disjoint S y
  disjoint X x
  disjoint X y
  disjoint g n
  disjoint g s
  disjoint g x
  disjoint g y
  disjoint G g
  disjoint n s
  disjoint n x
  disjoint n y
  disjoint G n
  disjoint s x
  disjoint s y
  disjoint G s
  disjoint N g
  disjoint N n
  disjoint N s
  disjoint S g
  disjoint S n
  disjoint S s
  disjoint X g
  disjoint X n
  disjoint X s
  disjoint Z g
  disjoint Z n
  disjoint Z s
  assert |- ( ( G e. _V /\ S e. _V /\ N e. _V ) -> ( <. <. G , S >. , N >. e. NrmCVec <-> ( <. G , S >. e. CVecOLD /\ N : X --> RR /\ A. x e. X ( ( ( N ` x ) = 0 -> x = Z ) /\ A. y e. CC ( N ` ( y S x ) ) = ( ( abs ` y ) x. ( N ` x ) ) /\ A. y e. X ( N ` ( x G y ) ) <_ ( ( N ` x ) + ( N ` y ) ) ) ) ) )

  proof
    cG
    cS
    cop
    #
    cN
    cop
    #
    cnv
    wcel
    @1
    vg
    cv
    #
    vs
    cv
    #
    cop
    #
    cvc
    wcel
    #
    @2
    crn
    #
    cr
    vn
    cv
    #
    wf
    #
    vx
    cv
    #
    @7
    cfv
    #
    cc0
    wceq
    #
    @9
    @2
    cgi
    cfv
    #
    wceq
    #
    wi
    #
    vy
    cv
    #
    @9
    @3
    co
    #
    @7
    cfv
    #
    @15
    cabs
    cfv
    #
    @10
    cmul
    co
    #
    wceq
    #
    vy
    cc
    wral
    #
    @9
    @15
    @2
    co
    #
    @7
    cfv
    #
    @10
    @15
    @7
    cfv
    #
    caddc
    co
    #
    cle
    wbr
    #
    vy
    @6
    wral
    #
    w3a
    #
    vx
    @6
    wral
    #
    w3a
    #
    vg
    vs
    vn
    coprab
    #
    wcel
    cG
    cvv
    wcel
    cS
    cvv
    wcel
    cN
    cvv
    wcel
    w3a
    @0
    cvc
    wcel
    #
    cX
    cr
    cN
    wf
    #
    @9
    cN
    cfv
    #
    cc0
    wceq
    #
    @9
    cZ
    wceq
    #
    wi
    #
    @15
    @9
    cS
    co
    #
    cN
    cfv
    #
    @18
    @34
    cmul
    co
    #
    wceq
    #
    vy
    cc
    wral
    #
    @9
    @15
    cG
    co
    #
    cN
    cfv
    #
    @34
    @15
    cN
    cfv
    #
    caddc
    co
    #
    cle
    wbr
    #
    vy
    cX
    wral
    #
    w3a
    #
    vx
    cX
    wral
    #
    w3a
    #
    cnv
    @31
    @1
    vx
    vy
    vg
    vn
    vs
    df-nv
    eleq2i
    @30
    cG
    @3
    cop
    #
    cvc
    wcel
    #
    cX
    cr
    @7
    wf
    #
    @11
    @36
    wi
    #
    @21
    @43
    @7
    cfv
    #
    @25
    cle
    wbr
    #
    vy
    cX
    wral
    #
    w3a
    #
    vx
    cX
    wral
    #
    w3a
    @32
    @54
    @55
    @38
    @7
    cfv
    #
    @19
    wceq
    #
    vy
    cc
    wral
    #
    @58
    w3a
    #
    vx
    cX
    wral
    #
    w3a
    @51
    vg
    vs
    vn
    cG
    cS
    cN
    cvv
    cvv
    cvv
    @2
    cG
    wceq
    #
    @5
    @53
    @8
    @54
    @29
    @60
    @66
    @4
    @52
    cvc
    @2
    cG
    @3
    opeq1
    eleq1d
    @66
    @6
    cX
    cr
    @7
    @66
    @6
    cG
    crn
    cX
    @2
    cG
    rneq
    isnvlem.1
    syl6eqr
    #
    feq2d
    @66
    @28
    @59
    vx
    @6
    cX
    @67
    @66
    @14
    @55
    @27
    @58
    @21
    @66
    @13
    @36
    @11
    @66
    @12
    cZ
    @9
    @66
    @12
    cG
    cgi
    cfv
    cZ
    @2
    cG
    cgi
    fveq2
    isnvlem.2
    syl6eqr
    eqeq2d
    imbi2d
    @66
    @26
    @57
    vy
    @6
    cX
    @67
    @66
    @23
    @56
    @25
    cle
    @66
    @22
    @43
    @7
    @9
    @15
    @2
    cG
    oveq
    fveq2d
    breq1d
    raleqbidv
    3anbi13d
    raleqbidv
    3anbi123d
    @3
    cS
    wceq
    #
    @53
    @32
    @60
    @65
    @54
    @68
    @52
    @0
    cvc
    @3
    cS
    cG
    opeq2
    eleq1d
    @68
    @59
    @64
    vx
    cX
    @68
    @21
    @63
    @55
    @58
    @68
    @20
    @62
    vy
    cc
    @68
    @17
    @61
    @19
    @68
    @16
    @38
    @7
    @15
    @9
    @3
    cS
    oveq
    fveq2d
    eqeq1d
    ralbidv
    3anbi2d
    ralbidv
    3anbi13d
    @7
    cN
    wceq
    #
    @54
    @33
    @65
    @50
    @32
    cX
    cr
    @7
    cN
    feq1
    @69
    @64
    @49
    vx
    cX
    @69
    @55
    @37
    @63
    @42
    @58
    @48
    @69
    @11
    @35
    @36
    @69
    @10
    @34
    cc0
    @9
    @7
    cN
    fveq1
    #
    eqeq1d
    imbi1d
    @69
    @62
    @41
    vy
    cc
    @69
    @61
    @39
    @19
    @40
    @38
    @7
    cN
    fveq1
    @69
    @10
    @34
    @18
    cmul
    @70
    oveq2d
    eqeq12d
    ralbidv
    @69
    @57
    @47
    vy
    cX
    @69
    @56
    @44
    @25
    @46
    cle
    @43
    @7
    cN
    fveq1
    @69
    @10
    @34
    @24
    @45
    caddc
    @70
    @15
    @7
    cN
    fveq1
    oveq12d
    breq12d
    ralbidv
    3anbi123d
    ralbidv
    3anbi23d
    eloprabg
    syl5bb
end
