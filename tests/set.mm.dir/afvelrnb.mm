include "wfn.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "cv.mm"
include "cafv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "fnrnafv.mm"
include "adantr.mm"
include "eleq2d.mm"
include "wb.mm"
include "eqeq1.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "rexbidv.mm"
include "elabg.mm"
include "adantl.mm"
include "bitrd.mm"

theorem afvelrnb
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
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
  assert |- ( ( F Fn A /\ B e. V ) -> ( B e. ran F <-> E. x e. A ( F ''' x ) = B ) )

  proof
    cF
    cA
    wfn
    #
    cB
    cV
    wcel
    #
    wa
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
    @5
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    @2
    @3
    @8
    cB
    @0
    @3
    @8
    wceq
    @1
    vx
    vy
    cA
    cF
    fnrnafv
    adantr
    eleq2d
    @1
    @9
    @11
    wb
    @0
    @7
    @11
    vy
    cB
    cV
    @4
    cB
    wceq
    #
    @6
    @10
    vx
    cA
    @12
    @6
    cB
    @5
    wceq
    @10
    @4
    cB
    @5
    eqeq1
    cB
    @5
    eqcom
    syl6bb
    rexbidv
    elabg
    adantl
    bitrd
end
