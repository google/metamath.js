include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "cuni.mm"
include "wrex.mm"
include "exancom.mm"
include "eluni.mm"
include "df-rex.mm"
include "3bitr4i.mm"

theorem eluni2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( A e. U. B <-> E. x e. B A e. x )

  proof
    cA
    vx
    cv
    #
    wcel
    #
    @0
    cB
    wcel
    #
    wa
    vx
    wex
    @2
    @1
    wa
    vx
    wex
    cA
    cB
    cuni
    wcel
    @1
    vx
    cB
    wrex
    @1
    @2
    vx
    exancom
    vx
    cA
    cB
    eluni
    @1
    vx
    cB
    df-rex
    3bitr4i
end
