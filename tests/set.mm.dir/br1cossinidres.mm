include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "cin.mm"
include "ccoss.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "wceq.mm"
include "br1cossinres.mm"
include "wb.mm"
include "cvv.mm"
include "ideq2.mm"
include "elv.mm"
include "anbi1i.mm"
include "anbi12i.mm"
include "rexbii.mm"
include "syl6bb.mm"

theorem br1cossinidres
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cV: class V
  let cW: class W

  disjoint A u
  disjoint B u
  disjoint C u
  disjoint R u
  disjoint V u
  disjoint W u
  assert |- ( ( B e. V /\ C e. W ) -> ( B ,~ ( R i^i ( _I |` A ) ) C <-> E. u e. A ( ( u = B /\ u R B ) /\ ( u = C /\ u R C ) ) ) )

  proof
    cB
    cV
    wcel
    cC
    cW
    wcel
    wa
    cB
    cC
    cR
    cid
    cA
    cres
    cin
    ccoss
    wbr
    vu
    cv
    #
    cB
    cid
    wbr
    #
    @0
    cB
    cR
    wbr
    #
    wa
    #
    @0
    cC
    cid
    wbr
    #
    @0
    cC
    cR
    wbr
    #
    wa
    #
    wa
    #
    vu
    cA
    wrex
    @0
    cB
    wceq
    #
    @2
    wa
    #
    @0
    cC
    wceq
    #
    @5
    wa
    #
    wa
    #
    vu
    cA
    wrex
    vu
    cA
    cB
    cC
    cR
    cid
    cV
    cW
    br1cossinres
    @7
    @12
    vu
    cA
    @3
    @9
    @6
    @11
    @1
    @8
    @2
    @1
    @8
    wb
    vu
    @0
    cB
    cvv
    ideq2
    elv
    anbi1i
    @4
    @10
    @5
    @4
    @10
    wb
    vu
    @0
    cC
    cvv
    ideq2
    elv
    anbi1i
    anbi12i
    rexbii
    syl6bb
end
