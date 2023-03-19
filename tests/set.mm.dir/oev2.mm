include "con0.mm"
include "wcel.mm"
include "coe.mm"
include "co.mm"
include "cvv.mm"
include "cv.mm"
include "comu.mm"
include "cmpt.mm"
include "c1o.mm"
include "crdg.mm"
include "cfv.mm"
include "cint.mm"
include "cdif.mm"
include "cun.mm"
include "cin.mm"
include "wceq.mm"
include "c0.mm"
include "wa.mm"
include "oveq12.mm"
include "oe0m0.mm"
include "syl6eq.mm"
include "fveq2.mm"
include "1on.mm"
include "elexi.mm"
include "rdg0.mm"
include "inteq.mm"
include "int0.mm"
include "ineq12d.mm"
include "inv1.mm"
include "a1i.mm"
include "sylan9eqr.mm"
include "eqtr4d.mm"
include "oveq1.mm"
include "oe0m1.mm"
include "biimpa.mm"
include "an32s.mm"
include "int0el.mm"
include "ineq2d.mm"
include "in0.mm"
include "adantl.mm"
include "oe0lem.mm"
include "difeq2d.mm"
include "difid.mm"
include "uneq2d.mm"
include "uncom.mm"
include "un0.mm"
include "3eqtr3g.mm"
include "oevn0.mm"
include "dif0.mm"
include "unv.mm"
include "syl6req.mm"
include "eqtrd.mm"

theorem oev2
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  assert |- ( ( A e. On /\ B e. On ) -> ( A ^o B ) = ( ( rec ( ( x e. _V |-> ( x .o A ) ) , 1o ) ` B ) i^i ( ( _V \ |^| A ) u. |^| B ) ) )

  proof
    cB
    con0
    wcel
    #
    cA
    cB
    coe
    co
    #
    cB
    vx
    cvv
    vx
    cv
    cA
    comu
    co
    cmpt
    #
    c1o
    crdg
    #
    cfv
    #
    cvv
    cA
    cint
    #
    cdif
    #
    cB
    cint
    #
    cun
    #
    cin
    #
    wceq
    cA
    @0
    cA
    c0
    wceq
    #
    wa
    #
    @1
    @4
    @7
    cin
    #
    @9
    @10
    @1
    @12
    wceq
    cB
    @10
    cB
    c0
    wceq
    #
    wa
    #
    @1
    c1o
    @12
    @14
    @1
    c0
    c0
    coe
    co
    c1o
    cA
    c0
    cB
    c0
    coe
    oveq12
    oe0m0
    syl6eq
    @13
    @10
    @12
    c1o
    cvv
    cin
    #
    c1o
    @13
    @4
    c1o
    @7
    cvv
    @13
    @4
    c0
    @3
    cfv
    c1o
    cB
    c0
    @3
    fveq2
    c1o
    @2
    c1o
    con0
    1on
    elexi
    rdg0
    syl6eq
    @13
    @7
    c0
    cint
    #
    cvv
    cB
    c0
    inteq
    int0
    syl6eq
    ineq12d
    @15
    c1o
    wceq
    @10
    c1o
    inv1
    a1i
    sylan9eqr
    eqtr4d
    @11
    c0
    cB
    wcel
    #
    wa
    @1
    c0
    @12
    @0
    @17
    @10
    @1
    c0
    wceq
    @10
    @0
    @17
    wa
    @1
    c0
    cB
    coe
    co
    #
    c0
    cA
    c0
    cB
    coe
    oveq1
    @0
    @17
    @18
    c0
    wceq
    cB
    oe0m1
    biimpa
    sylan9eqr
    an32s
    @17
    @12
    c0
    wceq
    @11
    @17
    @12
    @4
    c0
    cin
    c0
    @17
    @7
    c0
    @4
    cB
    int0el
    ineq2d
    @4
    in0
    syl6eq
    adantl
    eqtr4d
    oe0lem
    @11
    @8
    @7
    @4
    @10
    @8
    @7
    wceq
    @0
    @10
    @7
    @6
    cun
    #
    @7
    c0
    cun
    @8
    @7
    @10
    @6
    c0
    @7
    @10
    @6
    cvv
    cvv
    cdif
    c0
    @10
    @5
    cvv
    cvv
    @10
    @5
    @16
    cvv
    cA
    c0
    inteq
    int0
    syl6eq
    difeq2d
    cvv
    difid
    syl6eq
    uneq2d
    @7
    @6
    uncom
    #
    @7
    un0
    3eqtr3g
    adantl
    ineq2d
    eqtr4d
    cA
    con0
    wcel
    @0
    wa
    #
    c0
    cA
    wcel
    #
    wa
    #
    @1
    @4
    @9
    vx
    cA
    cB
    oevn0
    @23
    @9
    @4
    cvv
    cin
    @4
    @23
    @8
    cvv
    @4
    @22
    @8
    cvv
    wceq
    @21
    @22
    @19
    @7
    cvv
    cun
    @8
    cvv
    @22
    @6
    cvv
    @7
    @22
    @6
    cvv
    c0
    cdif
    cvv
    @22
    @5
    c0
    cvv
    cA
    int0el
    difeq2d
    cvv
    dif0
    syl6eq
    uneq2d
    @20
    @7
    unv
    3eqtr3g
    adantl
    ineq2d
    @4
    inv1
    syl6req
    eqtrd
    oe0lem
end
