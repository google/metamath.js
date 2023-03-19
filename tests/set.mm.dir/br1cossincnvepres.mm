include "wcel.mm"
include "wa.mm"
include "cep.mm"
include "ccnv.mm"
include "cres.mm"
include "cin.mm"
include "ccoss.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "br1cossinres.mm"
include "wb.mm"
include "cvv.mm"
include "brcnvep.mm"
include "elv.mm"
include "anbi1i.mm"
include "anbi12i.mm"
include "rexbii.mm"
include "syl6bb.mm"

theorem br1cossincnvepres
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
  assert |- ( ( B e. V /\ C e. W ) -> ( B ,~ ( R i^i ( `' _E |` A ) ) C <-> E. u e. A ( ( B e. u /\ u R B ) /\ ( C e. u /\ u R C ) ) ) )

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
    cep
    ccnv
    #
    cA
    cres
    cin
    ccoss
    wbr
    vu
    cv
    #
    cB
    @0
    wbr
    #
    @1
    cB
    cR
    wbr
    #
    wa
    #
    @1
    cC
    @0
    wbr
    #
    @1
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
    cB
    @1
    wcel
    #
    @3
    wa
    #
    cC
    @1
    wcel
    #
    @6
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
    @0
    cV
    cW
    br1cossinres
    @8
    @13
    vu
    cA
    @4
    @10
    @7
    @12
    @2
    @9
    @3
    @2
    @9
    wb
    vu
    @1
    cB
    cvv
    brcnvep
    elv
    anbi1i
    @5
    @11
    @6
    @5
    @11
    wb
    vu
    @1
    cC
    cvv
    brcnvep
    elv
    anbi1i
    anbi12i
    rexbii
    syl6bb
end
