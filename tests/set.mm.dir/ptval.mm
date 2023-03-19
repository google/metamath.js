include "wcel.mm"
include "wfn.mm"
include "wa.mm"
include "cv.mm"
include "cdm.mm"
include "cfv.mm"
include "wral.mm"
include "cuni.mm"
include "wceq.mm"
include "cdif.mm"
include "cfn.mm"
include "wrex.mm"
include "w3a.mm"
include "cixp.mm"
include "wex.mm"
include "cab.mm"
include "ctg.mm"
include "cvv.mm"
include "cpt.mm"
include "cmpt.mm"
include "df-pt.mm"
include "a1i.mm"
include "simpr.mm"
include "dmeqd.mm"
include "fndm.mm"
include "ad2antlr.mm"
include "eqtrd.mm"
include "fneq2d.mm"
include "fveq1d.mm"
include "eleq2d.mm"
include "raleqbidv.mm"
include "difeq1d.mm"
include "unieqd.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "3anbi123d.mm"
include "ixpeq1d.mm"
include "anbi12d.mm"
include "exbidv.mm"
include "abbidv.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "fnex.mm"
include "ancoms.mm"
include "fvexd.mm"
include "fvmptd.mm"

theorem ptval
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vg: setvar g
  let cF: class F
  let cV: class V
  let vf: setvar f
  assume ptval.1: |- B = { x | E. g ( ( g Fn A /\ A. y e. A ( g ` y ) e. ( F ` y ) /\ E. z e. Fin A. y e. ( A \ z ) ( g ` y ) = U. ( F ` y ) ) /\ x = X_ y e. A ( g ` y ) ) }

  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F g
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint V g
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint B f
  disjoint F f
  disjoint V f
  assert |- ( ( A e. V /\ F Fn A ) -> ( Xt_ ` F ) = ( topGen ` B ) )

  proof
    cA
    cV
    wcel
    #
    cF
    cA
    wfn
    #
    wa
    #
    vf
    cF
    vg
    cv
    #
    vf
    cv
    #
    cdm
    #
    wfn
    #
    vy
    cv
    #
    @3
    cfv
    #
    @7
    @4
    cfv
    #
    wcel
    #
    vy
    @5
    wral
    #
    @8
    @9
    cuni
    #
    wceq
    #
    vy
    @5
    vz
    cv
    #
    cdif
    #
    wral
    #
    vz
    cfn
    wrex
    #
    w3a
    #
    vx
    cv
    #
    vy
    @5
    @8
    cixp
    #
    wceq
    #
    wa
    #
    vg
    wex
    #
    vx
    cab
    #
    ctg
    cfv
    #
    cB
    ctg
    cfv
    cvv
    cpt
    cvv
    cpt
    vf
    cvv
    @25
    cmpt
    wceq
    @2
    vx
    vy
    vz
    vf
    vg
    df-pt
    a1i
    @2
    @4
    cF
    wceq
    #
    wa
    #
    @24
    cB
    ctg
    @27
    @24
    @3
    cA
    wfn
    #
    @8
    @7
    cF
    cfv
    #
    wcel
    #
    vy
    cA
    wral
    #
    @8
    @29
    cuni
    #
    wceq
    #
    vy
    cA
    @14
    cdif
    #
    wral
    #
    vz
    cfn
    wrex
    #
    w3a
    #
    @19
    vy
    cA
    @8
    cixp
    #
    wceq
    #
    wa
    #
    vg
    wex
    #
    vx
    cab
    cB
    @27
    @23
    @41
    vx
    @27
    @22
    @40
    vg
    @27
    @18
    @37
    @21
    @39
    @27
    @6
    @28
    @11
    @31
    @17
    @36
    @27
    @5
    cA
    @3
    @27
    @5
    cF
    cdm
    #
    cA
    @27
    @4
    cF
    @2
    @26
    simpr
    #
    dmeqd
    @1
    @42
    cA
    wceq
    @0
    @26
    cA
    cF
    fndm
    ad2antlr
    eqtrd
    #
    fneq2d
    @27
    @10
    @30
    vy
    @5
    cA
    @44
    @27
    @9
    @29
    @8
    @27
    @7
    @4
    cF
    @43
    fveq1d
    #
    eleq2d
    raleqbidv
    @27
    @16
    @35
    vz
    cfn
    @27
    @13
    @33
    vy
    @15
    @34
    @27
    @5
    cA
    @14
    @44
    difeq1d
    @27
    @12
    @32
    @8
    @27
    @9
    @29
    @45
    unieqd
    eqeq2d
    raleqbidv
    rexbidv
    3anbi123d
    @27
    @20
    @38
    @19
    @27
    vy
    @5
    cA
    @8
    @44
    ixpeq1d
    eqeq2d
    anbi12d
    exbidv
    abbidv
    ptval.1
    syl6eqr
    fveq2d
    @1
    @0
    cF
    cvv
    wcel
    cA
    cV
    cF
    fnex
    ancoms
    @2
    cB
    ctg
    fvexd
    fvmptd
end
