include "chil.mm"
include "clf.mm"
include "ccnfn.mm"
include "cin.mm"
include "cbr.mm"
include "wf1o.mm"
include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "csp.mm"
include "co.mm"
include "cmpt.mm"
include "ax-hilex.mm"
include "mptex.mm"
include "df-bra.mm"
include "fnmpti.mm"
include "rnbra.mm"
include "wcel.mm"
include "wa.mm"
include "fveq1.mm"
include "braval.mm"
include "adantlr.mm"
include "adantll.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "ralrimdva.mm"
include "hial2eq2.mm"
include "sylibd.mm"
include "rgen2a.mm"
include "dff1o6.mm"
include "mpbir3an.mm"

theorem bra11
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vt: setvar t
  let vu: setvar u
  let cT: class T
  let cU: class U


  assert |- bra : ~H -1-1-onto-> ( LinFn i^i ContFn )

  proof
    chil
    clf
    ccnfn
    cin
    #
    cbr
    wf1o
    cbr
    chil
    wfn
    cbr
    crn
    @0
    wceq
    vx
    cv
    #
    cbr
    cfv
    #
    vy
    cv
    #
    cbr
    cfv
    #
    wceq
    #
    @1
    @3
    wceq
    #
    wi
    #
    vy
    chil
    wral
    vx
    chil
    wral
    vx
    chil
    vy
    chil
    @3
    @1
    csp
    co
    #
    cmpt
    cbr
    vy
    chil
    @8
    ax-hilex
    mptex
    vx
    vy
    df-bra
    fnmpti
    rnbra
    @7
    vx
    vy
    chil
    @1
    chil
    wcel
    #
    @3
    chil
    wcel
    #
    wa
    #
    @5
    vz
    cv
    #
    @1
    csp
    co
    #
    @12
    @3
    csp
    co
    #
    wceq
    #
    vz
    chil
    wral
    @6
    @11
    @5
    @15
    vz
    chil
    @5
    @12
    @2
    cfv
    #
    @12
    @4
    cfv
    #
    wceq
    @11
    @12
    chil
    wcel
    #
    wa
    #
    @15
    @12
    @2
    @4
    fveq1
    @19
    @16
    @13
    @17
    @14
    @9
    @18
    @16
    @13
    wceq
    @10
    @1
    @12
    braval
    adantlr
    @10
    @18
    @17
    @14
    wceq
    @9
    @3
    @12
    braval
    adantll
    eqeq12d
    syl5ib
    ralrimdva
    vz
    @1
    @3
    hial2eq2
    sylibd
    rgen2a
    vx
    vy
    chil
    @0
    cbr
    dff1o6
    mpbir3an
end
