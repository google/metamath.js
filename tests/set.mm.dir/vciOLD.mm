include "cablo.mm"
include "wcel.mm"
include "cc.mm"
include "cxp.mm"
include "wf.mm"
include "c1.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "caddc.mm"
include "cmul.mm"
include "wa.mm"
include "w3a.mm"
include "crn.mm"
include "copab.mm"
include "cvc.mm"
include "c1st.mm"
include "cfv.mm"
include "wb.mm"
include "eqeq2i.mm"
include "eleq1.mm"
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
include "sylbir.mm"
include "c2nd.mm"
include "feq1.mm"
include "eqeq1d.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "3anbi23d.mm"
include "elopabi.mm"
include "df-vc.mm"
include "eleq2s.mm"

theorem vciOLD
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cS: class S
  let cG: class G
  let cW: class W
  let cX: class X
  let vg: setvar g
  let vs: setvar s
  let cA: class A
  let cB: class B
  let cC: class C
  assume vciOLD.1: |- G = ( 1st ` W )
  assume vciOLD.2: |- S = ( 2nd ` W )
  assume vciOLD.3: |- X = ran G

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
  disjoint X y
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
  disjoint W g
  disjoint W s
  disjoint X g
  disjoint X s
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  assert |- ( W e. CVecOLD -> ( G e. AbelOp /\ S : ( CC X. X ) --> X /\ A. x e. X ( ( 1 S x ) = x /\ A. y e. CC ( A. z e. X ( y S ( x G z ) ) = ( ( y S x ) G ( y S z ) ) /\ A. z e. CC ( ( ( y + z ) S x ) = ( ( y S x ) G ( z S x ) ) /\ ( ( y x. z ) S x ) = ( y S ( z S x ) ) ) ) ) ) )

  proof
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
    vx
    cv
    #
    cS
    co
    #
    @3
    wceq
    #
    vy
    cv
    #
    @3
    vz
    cv
    #
    cG
    co
    #
    cS
    co
    #
    @6
    @3
    cS
    co
    #
    @6
    @7
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
    @6
    @7
    caddc
    co
    #
    @3
    cS
    co
    #
    @10
    @7
    @3
    cS
    co
    #
    cG
    co
    #
    wceq
    #
    @6
    @7
    cmul
    co
    #
    @3
    cS
    co
    #
    @6
    @17
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
    cW
    vg
    cv
    #
    cablo
    wcel
    #
    cc
    @31
    crn
    #
    cxp
    #
    @33
    vs
    cv
    #
    wf
    #
    c1
    @3
    @35
    co
    #
    @3
    wceq
    #
    @6
    @3
    @7
    @31
    co
    #
    @35
    co
    #
    @6
    @3
    @35
    co
    #
    @6
    @7
    @35
    co
    #
    @31
    co
    #
    wceq
    #
    vz
    @33
    wral
    #
    @15
    @3
    @35
    co
    #
    @41
    @7
    @3
    @35
    co
    #
    @31
    co
    #
    wceq
    #
    @20
    @3
    @35
    co
    #
    @6
    @47
    @35
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
    @33
    wral
    #
    w3a
    #
    vg
    vs
    copab
    cvc
    @59
    @0
    @1
    cX
    @35
    wf
    #
    @38
    @6
    @8
    @35
    co
    #
    @41
    @42
    cG
    co
    #
    wceq
    #
    vz
    cX
    wral
    #
    @46
    @41
    @47
    cG
    co
    #
    wceq
    #
    @52
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
    @30
    vg
    vs
    cW
    @31
    cW
    c1st
    cfv
    #
    wceq
    @31
    cG
    wceq
    #
    @59
    @73
    wb
    cG
    @74
    @31
    vciOLD.1
    eqeq2i
    @75
    @32
    @0
    @36
    @60
    @58
    @72
    @31
    cG
    cablo
    eleq1
    @75
    @33
    cX
    wceq
    #
    @36
    @60
    wb
    @75
    @33
    cG
    crn
    cX
    @31
    cG
    rneq
    vciOLD.3
    syl6eqr
    #
    @76
    @36
    @1
    @33
    @35
    wf
    @60
    @76
    @34
    @1
    @33
    @35
    @33
    cX
    cc
    xpeq2
    feq2d
    @33
    cX
    @1
    @35
    feq3
    bitrd
    syl
    @75
    @57
    @71
    vx
    @33
    cX
    @77
    @75
    @56
    @70
    @38
    @75
    @55
    @69
    vy
    cc
    @75
    @45
    @64
    @54
    @68
    @75
    @44
    @63
    vz
    @33
    cX
    @77
    @75
    @40
    @61
    @43
    @62
    @75
    @39
    @8
    @6
    @35
    @3
    @7
    @31
    cG
    oveq
    oveq2d
    @41
    @42
    @31
    cG
    oveq
    eqeq12d
    raleqbidv
    @75
    @53
    @67
    vz
    cc
    @75
    @49
    @66
    @52
    @75
    @48
    @65
    @46
    @41
    @47
    @31
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
    sylbir
    @35
    cW
    c2nd
    cfv
    #
    wceq
    @35
    cS
    wceq
    #
    @73
    @30
    wb
    cS
    @78
    @35
    vciOLD.2
    eqeq2i
    @79
    @60
    @2
    @72
    @29
    @0
    @1
    cX
    @35
    cS
    feq1
    @79
    @71
    @28
    vx
    cX
    @79
    @38
    @5
    @70
    @27
    @79
    @37
    @4
    @3
    c1
    @3
    @35
    cS
    oveq
    eqeq1d
    @79
    @69
    @26
    vy
    cc
    @79
    @64
    @14
    @68
    @25
    @79
    @63
    @13
    vz
    cX
    @79
    @61
    @9
    @62
    @12
    @6
    @8
    @35
    cS
    oveq
    @79
    @41
    @10
    @42
    @11
    cG
    @6
    @3
    @35
    cS
    oveq
    #
    @6
    @7
    @35
    cS
    oveq
    oveq12d
    eqeq12d
    ralbidv
    @79
    @67
    @24
    vz
    cc
    @79
    @66
    @19
    @52
    @23
    @79
    @46
    @16
    @65
    @18
    @15
    @3
    @35
    cS
    oveq
    @79
    @41
    @10
    @47
    @17
    cG
    @80
    @7
    @3
    @35
    cS
    oveq
    #
    oveq12d
    eqeq12d
    @79
    @50
    @21
    @51
    @22
    @20
    @3
    @35
    cS
    oveq
    @79
    @51
    @6
    @17
    @35
    co
    @22
    @79
    @47
    @17
    @6
    @35
    @81
    oveq2d
    @6
    @17
    @35
    cS
    oveq
    eqtrd
    eqeq12d
    anbi12d
    ralbidv
    anbi12d
    ralbidv
    anbi12d
    ralbidv
    3anbi23d
    sylbir
    elopabi
    vx
    vy
    vz
    vg
    vs
    df-vc
    eleq2s
end
