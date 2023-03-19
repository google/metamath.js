include "word.mm"
include "cv.mm"
include "wss.mm"
include "con0.mm"
include "crab.mm"
include "cuni.mm"
include "csuc.mm"
include "cpw.mm"
include "cin.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "df-rab.mm"
include "incom.mm"
include "inab.mm"
include "df-pw.mm"
include "eqcomi.mm"
include "abid2.mm"
include "ineq12i.mm"
include "3eqtr3i.mm"
include "eqtri.mm"
include "ordpwsuc.mm"
include "syl5eq.mm"
include "unieqd.mm"
include "ordunisuc.mm"
include "eqtrd.mm"

theorem orduniss2
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( Ord A -> U. { x e. On | x C_ A } = A )

  proof
    cA
    word
    #
    vx
    cv
    #
    cA
    wss
    #
    vx
    con0
    crab
    #
    cuni
    cA
    csuc
    #
    cuni
    cA
    @0
    @3
    @4
    @0
    @3
    cA
    cpw
    #
    con0
    cin
    #
    @4
    @3
    @1
    con0
    wcel
    #
    @2
    wa
    vx
    cab
    #
    @6
    @2
    vx
    con0
    df-rab
    @7
    vx
    cab
    #
    @2
    vx
    cab
    #
    cin
    @10
    @9
    cin
    @8
    @6
    @9
    @10
    incom
    @7
    @2
    vx
    inab
    @10
    @5
    @9
    con0
    @5
    @10
    vx
    cA
    df-pw
    eqcomi
    vx
    con0
    abid2
    ineq12i
    3eqtr3i
    eqtri
    cA
    ordpwsuc
    syl5eq
    unieqd
    cA
    ordunisuc
    eqtrd
end
