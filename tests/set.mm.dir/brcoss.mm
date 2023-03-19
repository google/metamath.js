include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "ccoss.mm"
include "wceq.mm"
include "breq2.mm"
include "bi2anan9.mm"
include "exbidv.mm"
include "df-coss.mm"
include "brabga.mm"

theorem brcoss
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y

  disjoint A u
  disjoint B u
  disjoint R u
  disjoint V u
  disjoint W u
  disjoint A x
  disjoint A y
  disjoint u x
  disjoint u y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  assert |- ( ( A e. V /\ B e. W ) -> ( A ,~ R B <-> E. u ( u R A /\ u R B ) ) )

  proof
    vu
    cv
    #
    vx
    cv
    #
    cR
    wbr
    #
    @0
    vy
    cv
    #
    cR
    wbr
    #
    wa
    #
    vu
    wex
    @0
    cA
    cR
    wbr
    #
    @0
    cB
    cR
    wbr
    #
    wa
    #
    vu
    wex
    vx
    vy
    cA
    cB
    cR
    ccoss
    cV
    cW
    @1
    cA
    wceq
    #
    @3
    cB
    wceq
    #
    wa
    @5
    @8
    vu
    @9
    @2
    @6
    @10
    @4
    @7
    @1
    cA
    @0
    cR
    breq2
    @3
    cB
    @0
    cR
    breq2
    bi2anan9
    exbidv
    vx
    vy
    vu
    cR
    df-coss
    brabga
end
