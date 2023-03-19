include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wrex.mm"
include "ccoels.mm"
include "wceq.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "rexbidv.mm"
include "dfcoels.mm"
include "brabga.mm"

theorem brcoels
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y

  disjoint A u
  disjoint B u
  disjoint C u
  disjoint A x
  disjoint A y
  disjoint u x
  disjoint u y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  assert |- ( ( B e. V /\ C e. W ) -> ( B ~ A C <-> E. u e. A ( B e. u /\ C e. u ) ) )

  proof
    vx
    cv
    #
    vu
    cv
    #
    wcel
    #
    vy
    cv
    #
    @1
    wcel
    #
    wa
    #
    vu
    cA
    wrex
    cB
    @1
    wcel
    #
    cC
    @1
    wcel
    #
    wa
    #
    vu
    cA
    wrex
    vx
    vy
    cB
    cC
    cA
    ccoels
    cV
    cW
    @0
    cB
    wceq
    #
    @3
    cC
    wceq
    #
    wa
    @5
    @8
    vu
    cA
    @9
    @2
    @6
    @10
    @4
    @7
    @0
    cB
    @1
    eleq1
    @3
    cC
    @1
    eleq1
    bi2anan9
    rexbidv
    vx
    vy
    vu
    cA
    dfcoels
    brabga
end
