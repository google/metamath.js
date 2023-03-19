include "csur.mm"
include "wcel.mm"
include "wa.mm"
include "cslt.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "c1o.mm"
include "c0.mm"
include "cop.mm"
include "c2o.mm"
include "ctp.mm"
include "con0.mm"
include "wrex.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "anbi2d.mm"
include "eqeq2d.mm"
include "breq2d.mm"
include "df-slt.mm"
include "brabg.mm"
include "bianabs.mm"

theorem sltval
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vg: setvar g

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint A f
  disjoint A g
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint g x
  disjoint g y
  disjoint B f
  disjoint B g
  assert |- ( ( A e. No /\ B e. No ) -> ( A <s B <-> E. x e. On ( A. y e. x ( A ` y ) = ( B ` y ) /\ ( A ` x ) { <. 1o , (/) >. , <. 1o , 2o >. , <. (/) , 2o >. } ( B ` x ) ) ) )

  proof
    cA
    csur
    wcel
    #
    cB
    csur
    wcel
    #
    wa
    #
    cA
    cB
    cslt
    wbr
    vy
    cv
    #
    cA
    cfv
    #
    @3
    cB
    cfv
    #
    wceq
    #
    vy
    vx
    cv
    #
    wral
    #
    @7
    cA
    cfv
    #
    @7
    cB
    cfv
    #
    c1o
    c0
    cop
    c1o
    c2o
    cop
    c0
    c2o
    cop
    ctp
    #
    wbr
    #
    wa
    #
    vx
    con0
    wrex
    #
    vf
    cv
    #
    csur
    wcel
    #
    vg
    cv
    #
    csur
    wcel
    #
    wa
    #
    @3
    @15
    cfv
    #
    @3
    @17
    cfv
    #
    wceq
    #
    vy
    @7
    wral
    #
    @7
    @15
    cfv
    #
    @7
    @17
    cfv
    #
    @11
    wbr
    #
    wa
    #
    vx
    con0
    wrex
    #
    wa
    @0
    @18
    wa
    #
    @4
    @21
    wceq
    #
    vy
    @7
    wral
    #
    @9
    @25
    @11
    wbr
    #
    wa
    #
    vx
    con0
    wrex
    #
    wa
    @2
    @14
    wa
    vf
    vg
    cA
    cB
    csur
    csur
    cslt
    @15
    cA
    wceq
    #
    @19
    @29
    @28
    @34
    @35
    @16
    @0
    @18
    @15
    cA
    csur
    eleq1
    anbi1d
    @35
    @27
    @33
    vx
    con0
    @35
    @23
    @31
    @26
    @32
    @35
    @22
    @30
    vy
    @7
    @35
    @20
    @4
    @21
    @3
    @15
    cA
    fveq1
    eqeq1d
    ralbidv
    @35
    @24
    @9
    @25
    @11
    @7
    @15
    cA
    fveq1
    breq1d
    anbi12d
    rexbidv
    anbi12d
    @17
    cB
    wceq
    #
    @29
    @2
    @34
    @14
    @36
    @18
    @1
    @0
    @17
    cB
    csur
    eleq1
    anbi2d
    @36
    @33
    @13
    vx
    con0
    @36
    @31
    @8
    @32
    @12
    @36
    @30
    @6
    vy
    @7
    @36
    @21
    @5
    @4
    @3
    @17
    cB
    fveq1
    eqeq2d
    ralbidv
    @36
    @25
    @10
    @9
    @11
    @7
    @17
    cB
    fveq1
    breq2d
    anbi12d
    rexbidv
    anbi12d
    vx
    vy
    vf
    vg
    df-slt
    brabg
    bianabs
end
