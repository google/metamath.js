include "wcel.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "ccrd.mm"
include "cdm.mm"
include "cvv.mm"
include "elex.mm"
include "cima.mm"
include "cdif.mm"
include "con0.mm"
include "wa.mm"
include "w3a.mm"
include "wss.mm"
include "difss.mm"
include "elpw2g.mm"
include "mpbiri.mm"
include "wceq.mm"
include "neeq1.mm"
include "fveq2.mm"
include "id.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl.mm"
include "3imp.mm"
include "cres.mm"
include "tfr2.mm"
include "wfun.mm"
include "wfn.mm"
include "tfr1.mm"
include "fnfun.mm"
include "ax-mp.mm"
include "vex.mm"
include "resfunexg.mm"
include "mp2an.mm"
include "crn.mm"
include "rneq.mm"
include "df-ima.mm"
include "syl6eqr.mm"
include "difeq2d.mm"
include "fveq2d.mm"
include "fvex.mm"
include "fvmpt.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "3expia.mm"
include "com23.mm"
include "ralrimiv.mm"
include "ex.mm"
include "wf1o.mm"
include "wrex.mm"
include "tz7.49c.mm"
include "cen.mm"
include "wbr.mm"
include "f1oen.mm"
include "isnumi.mm"
include "sylan2.mm"
include "rexlimiva.mm"
include "syl6.mm"
include "syld.mm"
include "exlimdv.mm"

theorem dfac8alem
  let vy: setvar y
  let cA: class A
  let cC: class C
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cG: class G
  let vx: setvar x
  assume dfac8alem.2: |- F = recs ( G )
  assume dfac8alem.3: |- G = ( f e. _V |-> ( g ` ( A \ ran f ) ) )

  disjoint f g
  disjoint f y
  disjoint A f
  disjoint g y
  disjoint A g
  disjoint A y
  disjoint C g
  disjoint F f
  disjoint F y
  disjoint f x
  disjoint g x
  disjoint x y
  disjoint A x
  disjoint F x
  assert |- ( A e. C -> ( E. g A. y e. ~P A ( y =/= (/) -> ( g ` y ) e. y ) -> A e. dom card ) )

  proof
    cA
    cC
    wcel
    #
    vy
    cv
    #
    c0
    wne
    #
    @1
    vg
    cv
    #
    cfv
    #
    @1
    wcel
    #
    wi
    #
    vy
    cA
    cpw
    #
    wral
    #
    cA
    ccrd
    cdm
    wcel
    #
    vg
    @0
    cA
    cvv
    wcel
    #
    @8
    @9
    wi
    cA
    cC
    elex
    @10
    @8
    cA
    cF
    vx
    cv
    #
    cima
    #
    cdif
    #
    c0
    wne
    #
    @11
    cF
    cfv
    #
    @13
    wcel
    #
    wi
    #
    vx
    con0
    wral
    #
    @9
    @10
    @8
    @18
    @10
    @8
    wa
    #
    @17
    vx
    con0
    @19
    @14
    @11
    con0
    wcel
    #
    @16
    @10
    @8
    @14
    @20
    @16
    wi
    @10
    @8
    @14
    w3a
    @16
    @20
    @13
    @3
    cfv
    #
    @13
    wcel
    #
    @10
    @8
    @14
    @22
    @10
    @13
    @7
    wcel
    #
    @8
    @14
    @22
    wi
    #
    wi
    @10
    @23
    @13
    cA
    wss
    cA
    @12
    difss
    @13
    cA
    cvv
    elpw2g
    mpbiri
    @6
    @24
    vy
    @13
    @7
    @1
    @13
    wceq
    #
    @2
    @14
    @5
    @22
    @1
    @13
    c0
    neeq1
    @25
    @4
    @21
    @1
    @13
    @1
    @13
    @3
    fveq2
    @25
    id
    eleq12d
    imbi12d
    rspcv
    syl
    3imp
    @20
    @15
    @21
    @13
    @20
    @15
    cF
    @11
    cres
    #
    cG
    cfv
    #
    @21
    @11
    cF
    cG
    dfac8alem.2
    tfr2
    @26
    cvv
    wcel
    #
    @27
    @21
    wceq
    cF
    wfun
    #
    @11
    cvv
    wcel
    @28
    cF
    con0
    wfn
    @29
    cF
    cG
    dfac8alem.2
    tfr1
    #
    con0
    cF
    fnfun
    ax-mp
    vx
    vex
    #
    cF
    @11
    cvv
    resfunexg
    mp2an
    vf
    @26
    cA
    vf
    cv
    #
    crn
    #
    cdif
    #
    @3
    cfv
    @21
    cvv
    cG
    @32
    @26
    wceq
    #
    @34
    @13
    @3
    @35
    @33
    @12
    cA
    @35
    @33
    @26
    crn
    @12
    @32
    @26
    rneq
    cF
    @11
    df-ima
    syl6eqr
    difeq2d
    fveq2d
    dfac8alem.3
    @13
    @3
    fvex
    fvmpt
    ax-mp
    syl6eq
    eleq1d
    syl5ibrcom
    3expia
    com23
    ralrimiv
    ex
    @10
    @18
    @11
    cA
    @26
    wf1o
    #
    vx
    con0
    wrex
    #
    @9
    @10
    @18
    @37
    vx
    cA
    cvv
    cF
    @30
    tz7.49c
    ex
    @36
    @9
    vx
    con0
    @36
    @20
    @11
    cA
    cen
    wbr
    @9
    @11
    cA
    @26
    @31
    f1oen
    @11
    cA
    isnumi
    sylan2
    rexlimiva
    syl6
    syld
    syl
    exlimdv
end
