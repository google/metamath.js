include "cop.mm"
include "cvc.mm"
include "wcel.mm"
include "cv.mm"
include "cablo.mm"
include "cc.mm"
include "crn.mm"
include "cxp.mm"
include "wf.mm"
include "c1.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "caddc.mm"
include "cmul.mm"
include "wa.mm"
include "w3a.mm"
include "copab.mm"
include "cvv.mm"
include "df-vc.mm"
include "eleq2i.mm"
include "eleq1.mm"
include "wb.mm"
include "rneq.mm"
include "syl6eqr.mm"
include "xpeq2.mm"
include "feq2d.mm"
include "feq3.mm"
include "bitrd.mm"
include "syl.mm"
include "oveq.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "raleqbidv.mm"
include "eqeq2d.mm"
include "anbi1d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "3anbi123d.mm"
include "feq1.mm"
include "eqeq1d.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "3anbi23d.mm"
include "opelopabg.mm"
include "syl5bb.mm"

theorem isvclem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cS: class S
  let cG: class G
  let cX: class X
  let vg: setvar g
  let vs: setvar s
  assume isvclem.1: |- X = ran G

  disjoint x y
  disjoint x z
  disjoint G x
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint X x
  disjoint X z
  disjoint g s
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint G g
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint G s
  disjoint S g
  disjoint S s
  disjoint X g
  disjoint X s
  assert |- ( ( G e. _V /\ S e. _V ) -> ( <. G , S >. e. CVecOLD <-> ( G e. AbelOp /\ S : ( CC X. X ) --> X /\ A. x e. X ( ( 1 S x ) = x /\ A. y e. CC ( A. z e. X ( y S ( x G z ) ) = ( ( y S x ) G ( y S z ) ) /\ A. z e. CC ( ( ( y + z ) S x ) = ( ( y S x ) G ( z S x ) ) /\ ( ( y x. z ) S x ) = ( y S ( z S x ) ) ) ) ) ) ) )

  proof
    cG
    cS
    cop
    #
    cvc
    wcel
    @0
    vg
    cv
    #
    cablo
    wcel
    #
    cc
    @1
    crn
    #
    cxp
    #
    @3
    vs
    cv
    #
    wf
    #
    c1
    vx
    cv
    #
    @5
    co
    #
    @7
    wceq
    #
    vy
    cv
    #
    @7
    vz
    cv
    #
    @1
    co
    #
    @5
    co
    #
    @10
    @7
    @5
    co
    #
    @10
    @11
    @5
    co
    #
    @1
    co
    #
    wceq
    #
    vz
    @3
    wral
    #
    @10
    @11
    caddc
    co
    #
    @7
    @5
    co
    #
    @14
    @11
    @7
    @5
    co
    #
    @1
    co
    #
    wceq
    #
    @10
    @11
    cmul
    co
    #
    @7
    @5
    co
    #
    @10
    @21
    @5
    co
    #
    wceq
    #
    wa
    #
    vz
    cc
    wral
    #
    wa
    #
    vy
    cc
    wral
    #
    wa
    #
    vx
    @3
    wral
    #
    w3a
    #
    vg
    vs
    copab
    #
    wcel
    cG
    cvv
    wcel
    cS
    cvv
    wcel
    wa
    cG
    cablo
    wcel
    #
    cc
    cX
    cxp
    #
    cX
    cS
    wf
    #
    c1
    @7
    cS
    co
    #
    @7
    wceq
    #
    @10
    @7
    @11
    cG
    co
    #
    cS
    co
    #
    @10
    @7
    cS
    co
    #
    @10
    @11
    cS
    co
    #
    cG
    co
    #
    wceq
    #
    vz
    cX
    wral
    #
    @19
    @7
    cS
    co
    #
    @43
    @11
    @7
    cS
    co
    #
    cG
    co
    #
    wceq
    #
    @24
    @7
    cS
    co
    #
    @10
    @49
    cS
    co
    #
    wceq
    #
    wa
    #
    vz
    cc
    wral
    #
    wa
    #
    vy
    cc
    wral
    #
    wa
    #
    vx
    cX
    wral
    #
    w3a
    #
    cvc
    @35
    @0
    vx
    vy
    vz
    vg
    vs
    df-vc
    eleq2i
    @34
    @36
    @37
    cX
    @5
    wf
    #
    @9
    @10
    @41
    @5
    co
    #
    @14
    @15
    cG
    co
    #
    wceq
    #
    vz
    cX
    wral
    #
    @20
    @14
    @21
    cG
    co
    #
    wceq
    #
    @27
    wa
    #
    vz
    cc
    wral
    #
    wa
    #
    vy
    cc
    wral
    #
    wa
    #
    vx
    cX
    wral
    #
    w3a
    @61
    vg
    vs
    cG
    cS
    cvv
    cvv
    @1
    cG
    wceq
    #
    @2
    @36
    @6
    @62
    @33
    @74
    @1
    cG
    cablo
    eleq1
    @75
    @3
    cX
    wceq
    #
    @6
    @62
    wb
    @75
    @3
    cG
    crn
    cX
    @1
    cG
    rneq
    isvclem.1
    syl6eqr
    #
    @76
    @6
    @37
    @3
    @5
    wf
    @62
    @76
    @4
    @37
    @3
    @5
    @3
    cX
    cc
    xpeq2
    feq2d
    @3
    cX
    @37
    @5
    feq3
    bitrd
    syl
    @75
    @32
    @73
    vx
    @3
    cX
    @77
    @75
    @31
    @72
    @9
    @75
    @30
    @71
    vy
    cc
    @75
    @18
    @66
    @29
    @70
    @75
    @17
    @65
    vz
    @3
    cX
    @77
    @75
    @13
    @63
    @16
    @64
    @75
    @12
    @41
    @10
    @5
    @7
    @11
    @1
    cG
    oveq
    oveq2d
    @14
    @15
    @1
    cG
    oveq
    eqeq12d
    raleqbidv
    @75
    @28
    @69
    vz
    cc
    @75
    @23
    @68
    @27
    @75
    @22
    @67
    @20
    @14
    @21
    @1
    cG
    oveq
    eqeq2d
    anbi1d
    ralbidv
    anbi12d
    ralbidv
    anbi2d
    raleqbidv
    3anbi123d
    @5
    cS
    wceq
    #
    @62
    @38
    @74
    @60
    @36
    @37
    cX
    @5
    cS
    feq1
    @78
    @73
    @59
    vx
    cX
    @78
    @9
    @40
    @72
    @58
    @78
    @8
    @39
    @7
    c1
    @7
    @5
    cS
    oveq
    eqeq1d
    @78
    @71
    @57
    vy
    cc
    @78
    @66
    @47
    @70
    @56
    @78
    @65
    @46
    vz
    cX
    @78
    @63
    @42
    @64
    @45
    @10
    @41
    @5
    cS
    oveq
    @78
    @14
    @43
    @15
    @44
    cG
    @10
    @7
    @5
    cS
    oveq
    #
    @10
    @11
    @5
    cS
    oveq
    oveq12d
    eqeq12d
    ralbidv
    @78
    @69
    @55
    vz
    cc
    @78
    @68
    @51
    @27
    @54
    @78
    @20
    @48
    @67
    @50
    @19
    @7
    @5
    cS
    oveq
    @78
    @14
    @43
    @21
    @49
    cG
    @79
    @11
    @7
    @5
    cS
    oveq
    #
    oveq12d
    eqeq12d
    @78
    @25
    @52
    @26
    @53
    @24
    @7
    @5
    cS
    oveq
    @78
    @26
    @10
    @21
    cS
    co
    @53
    @10
    @21
    @5
    cS
    oveq
    @78
    @21
    @49
    @10
    cS
    @80
    oveq2d
    eqtrd
    eqeq12d
    anbi12d
    ralbidv
    anbi12d
    ralbidv
    anbi12d
    ralbidv
    3anbi23d
    opelopabg
    syl5bb
end
