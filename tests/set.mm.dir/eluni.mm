include "cuni.mm"
include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "wa.mm"
include "wex.mm"
include "elex.mm"
include "adantr.mm"
include "exlimiv.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "df-uni.mm"
include "elab2g.mm"
include "pm5.21nii.mm"

theorem eluni
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( A e. U. B <-> E. x ( A e. x /\ x e. B ) )

  proof
    cA
    cB
    cuni
    #
    wcel
    cA
    cvv
    wcel
    #
    cA
    vx
    cv
    #
    wcel
    #
    @2
    cB
    wcel
    #
    wa
    #
    vx
    wex
    #
    cA
    @0
    elex
    @5
    @1
    vx
    @3
    @1
    @4
    cA
    @2
    elex
    adantr
    exlimiv
    vy
    cv
    #
    @2
    wcel
    #
    @4
    wa
    #
    vx
    wex
    @6
    vy
    cA
    @0
    cvv
    @7
    cA
    wceq
    #
    @9
    @5
    vx
    @10
    @8
    @3
    @4
    @7
    cA
    @2
    eleq1
    anbi1d
    exbidv
    vy
    vx
    cB
    df-uni
    elab2g
    pm5.21nii
end
