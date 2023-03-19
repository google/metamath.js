include "cop.mm"
include "ccphlo.mm"
include "wcel.mm"
include "cnv.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "c1.mm"
include "cneg.mm"
include "caddc.mm"
include "cmul.mm"
include "wceq.mm"
include "crn.mm"
include "wral.mm"
include "coprab.mm"
include "wa.mm"
include "w3a.mm"
include "df-ph.mm"
include "elin2.mm"
include "rneq.mm"
include "syl6eqr.mm"
include "oveq.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "eqeq1d.mm"
include "raleqbidv.mm"
include "oveq2d.mm"
include "2ralbidv.mm"
include "fveq1.mm"
include "eqeq12d.mm"
include "eloprabg.mm"
include "anbi2d.mm"
include "syl5bb.mm"

theorem isphg
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cG: class G
  let cN: class N
  let cX: class X
  let vg: setvar g
  let vn: setvar n
  let vs: setvar s
  assume isphg.1: |- X = ran G

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
  assert |- ( ( G e. A /\ S e. B /\ N e. C ) -> ( <. <. G , S >. , N >. e. CPreHilOLD <-> ( <. <. G , S >. , N >. e. NrmCVec /\ A. x e. X A. y e. X ( ( ( N ` ( x G y ) ) ^ 2 ) + ( ( N ` ( x G ( -u 1 S y ) ) ) ^ 2 ) ) = ( 2 x. ( ( ( N ` x ) ^ 2 ) + ( ( N ` y ) ^ 2 ) ) ) ) ) )

  proof
    cG
    cS
    cop
    cN
    cop
    #
    ccphlo
    wcel
    @0
    cnv
    wcel
    #
    @0
    vx
    cv
    #
    vy
    cv
    #
    vg
    cv
    #
    co
    #
    vn
    cv
    #
    cfv
    #
    c2
    cexp
    co
    #
    @2
    c1
    cneg
    #
    @3
    vs
    cv
    #
    co
    #
    @4
    co
    #
    @6
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    c2
    @2
    @6
    cfv
    #
    c2
    cexp
    co
    #
    @3
    @6
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    cmul
    co
    #
    wceq
    #
    vy
    @4
    crn
    #
    wral
    #
    vx
    @23
    wral
    #
    vg
    vs
    vn
    coprab
    #
    wcel
    #
    wa
    cG
    cA
    wcel
    cS
    cB
    wcel
    cN
    cC
    wcel
    w3a
    #
    @1
    @2
    @3
    cG
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    @2
    @9
    @3
    cS
    co
    #
    cG
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    c2
    @2
    cN
    cfv
    #
    c2
    cexp
    co
    #
    @3
    cN
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    cmul
    co
    #
    wceq
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    wa
    @0
    cnv
    @26
    ccphlo
    vx
    vy
    vg
    vn
    vs
    df-ph
    elin2
    @28
    @27
    @44
    @1
    @25
    @29
    @6
    cfv
    #
    c2
    cexp
    co
    #
    @2
    @11
    cG
    co
    #
    @6
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    @21
    wceq
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    @46
    @33
    @6
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    @21
    wceq
    #
    vy
    cX
    wral
    vx
    cX
    wral
    @44
    vg
    vs
    vn
    cG
    cS
    cN
    cA
    cB
    cC
    @4
    cG
    wceq
    #
    @24
    @52
    vx
    @23
    cX
    @57
    @23
    cG
    crn
    cX
    @4
    cG
    rneq
    isphg.1
    syl6eqr
    #
    @57
    @22
    @51
    vy
    @23
    cX
    @58
    @57
    @15
    @50
    @21
    @57
    @8
    @46
    @14
    @49
    caddc
    @57
    @7
    @45
    c2
    cexp
    @57
    @5
    @29
    @6
    @2
    @3
    @4
    cG
    oveq
    fveq2d
    oveq1d
    @57
    @13
    @48
    c2
    cexp
    @57
    @12
    @47
    @6
    @2
    @11
    @4
    cG
    oveq
    fveq2d
    oveq1d
    oveq12d
    eqeq1d
    raleqbidv
    raleqbidv
    @10
    cS
    wceq
    #
    @51
    @56
    vx
    vy
    cX
    cX
    @59
    @50
    @55
    @21
    @59
    @49
    @54
    @46
    caddc
    @59
    @48
    @53
    c2
    cexp
    @59
    @47
    @33
    @6
    @59
    @11
    @32
    @2
    cG
    @9
    @3
    @10
    cS
    oveq
    oveq2d
    fveq2d
    oveq1d
    oveq2d
    eqeq1d
    2ralbidv
    @6
    cN
    wceq
    #
    @56
    @43
    vx
    vy
    cX
    cX
    @60
    @55
    @36
    @21
    @42
    @60
    @46
    @31
    @54
    @35
    caddc
    @60
    @45
    @30
    c2
    cexp
    @29
    @6
    cN
    fveq1
    oveq1d
    @60
    @53
    @34
    c2
    cexp
    @33
    @6
    cN
    fveq1
    oveq1d
    oveq12d
    @60
    @20
    @41
    c2
    cmul
    @60
    @17
    @38
    @19
    @40
    caddc
    @60
    @16
    @37
    c2
    cexp
    @2
    @6
    cN
    fveq1
    oveq1d
    @60
    @18
    @39
    c2
    cexp
    @3
    @6
    cN
    fveq1
    oveq1d
    oveq12d
    oveq2d
    eqeq12d
    2ralbidv
    eloprabg
    anbi2d
    syl5bb
end
