include "cv.mm"
include "cxrn.mm"
include "ccnv.mm"
include "ccoss.mm"
include "wbr.mm"
include "copab.mm"
include "cin.mm"
include "wa.mm"
include "wb.mm"
include "cvv.mm"
include "br1cosscnvxrn.mm"
include "el2v.mm"
include "opabbii.mm"
include "inopab.mm"
include "eqtr4i.mm"
include "wrel.mm"
include "wceq.mm"
include "relcoss.mm"
include "dfrel4v.mm"
include "mpbi.mm"
include "ineq12i.mm"
include "3eqtr4i.mm"

theorem 1cosscnvxrn
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ,~ `' ( A |X. B ) = ( ,~ `' A i^i ,~ `' B )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cA
    cB
    cxrn
    ccnv
    #
    ccoss
    #
    wbr
    #
    vx
    vy
    copab
    #
    @0
    @1
    cA
    ccnv
    #
    ccoss
    #
    wbr
    #
    vx
    vy
    copab
    #
    @0
    @1
    cB
    ccnv
    #
    ccoss
    #
    wbr
    #
    vx
    vy
    copab
    #
    cin
    #
    @3
    @7
    @11
    cin
    @5
    @8
    @12
    wa
    #
    vx
    vy
    copab
    @14
    @4
    @15
    vx
    vy
    @4
    @15
    wb
    vx
    vy
    @0
    @1
    cA
    cB
    cvv
    cvv
    br1cosscnvxrn
    el2v
    opabbii
    @8
    @12
    vx
    vy
    inopab
    eqtr4i
    @3
    wrel
    @3
    @5
    wceq
    @2
    relcoss
    vx
    vy
    @3
    dfrel4v
    mpbi
    @7
    @9
    @11
    @13
    @7
    wrel
    @7
    @9
    wceq
    @6
    relcoss
    vx
    vy
    @7
    dfrel4v
    mpbi
    @11
    wrel
    @11
    @13
    wceq
    @10
    relcoss
    vx
    vy
    @11
    dfrel4v
    mpbi
    ineq12i
    3eqtr4i
end
