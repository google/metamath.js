include "con0.mm"
include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "c1o.mm"
include "cdif.mm"
include "cvv.mm"
include "comu.mm"
include "co.mm"
include "cmpt.mm"
include "crdg.mm"
include "cfv.mm"
include "cif.mm"
include "coe.mm"
include "eqeq1.mm"
include "oveq2.mm"
include "mpteq2dv.mm"
include "rdgeq1.mm"
include "syl.mm"
include "fveq1d.mm"
include "ifbieq2d.mm"
include "difeq2.mm"
include "fveq2.mm"
include "ifeq12d.mm"
include "df-oexp.mm"
include "1on.mm"
include "elexi.mm"
include "difss.mm"
include "ssexi.mm"
include "fvex.mm"
include "ifex.mm"
include "ovmpt2.mm"

theorem oev
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  assert |- ( ( A e. On /\ B e. On ) -> ( A ^o B ) = if ( A = (/) , ( 1o \ B ) , ( rec ( ( x e. _V |-> ( x .o A ) ) , 1o ) ` B ) ) )

  proof
    vy
    vz
    cA
    cB
    con0
    con0
    vy
    cv
    #
    c0
    wceq
    #
    c1o
    vz
    cv
    #
    cdif
    #
    @2
    vx
    cvv
    vx
    cv
    #
    @0
    comu
    co
    #
    cmpt
    #
    c1o
    crdg
    #
    cfv
    #
    cif
    cA
    c0
    wceq
    #
    c1o
    cB
    cdif
    #
    cB
    vx
    cvv
    @4
    cA
    comu
    co
    #
    cmpt
    #
    c1o
    crdg
    #
    cfv
    #
    cif
    coe
    @9
    @3
    @2
    @13
    cfv
    #
    cif
    @0
    cA
    wceq
    #
    @1
    @9
    @8
    @15
    @3
    @0
    cA
    c0
    eqeq1
    @16
    @2
    @7
    @13
    @16
    @6
    @12
    wceq
    @7
    @13
    wceq
    @16
    vx
    cvv
    @5
    @11
    @0
    cA
    @4
    comu
    oveq2
    mpteq2dv
    c1o
    @6
    @12
    rdgeq1
    syl
    fveq1d
    ifbieq2d
    @2
    cB
    wceq
    @9
    @3
    @10
    @15
    @14
    @2
    cB
    c1o
    difeq2
    @2
    cB
    @13
    fveq2
    ifeq12d
    vy
    vz
    vx
    df-oexp
    @9
    @10
    @14
    @10
    c1o
    c1o
    con0
    1on
    elexi
    c1o
    cB
    difss
    ssexi
    cB
    @13
    fvex
    ifex
    ovmpt2
end
