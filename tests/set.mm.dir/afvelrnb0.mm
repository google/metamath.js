include "wfn.mm"
include "crn.mm"
include "wcel.mm"
include "cv.mm"
include "cafv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "fnrnafv.mm"
include "eleq2d.mm"
include "eqeq1.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "rexbidv.mm"
include "elabg.mm"
include "ibi.mm"
include "syl6bi.mm"

theorem afvelrnb0
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y
  let vk: setvar k

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint F y
  disjoint k x
  assert |- ( F Fn A -> ( B e. ran F -> E. x e. A ( F ''' x ) = B ) )

  proof
    cF
    cA
    wfn
    #
    cB
    cF
    crn
    #
    wcel
    cB
    vy
    cv
    #
    vx
    cv
    cF
    cafv
    #
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cab
    #
    wcel
    #
    @3
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    @0
    @1
    @6
    cB
    vx
    vy
    cA
    cF
    fnrnafv
    eleq2d
    @7
    @9
    @5
    @9
    vy
    cB
    @6
    @2
    cB
    wceq
    #
    @4
    @8
    vx
    cA
    @10
    @4
    cB
    @3
    wceq
    @8
    @2
    cB
    @3
    eqeq1
    cB
    @3
    eqcom
    syl6bb
    rexbidv
    elabg
    ibi
    syl6bi
end
