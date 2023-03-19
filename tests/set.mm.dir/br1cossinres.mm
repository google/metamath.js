include "cres.mm"
include "cin.mm"
include "ccoss.mm"
include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "inres.mm"
include "cosseqi.mm"
include "breqi.mm"
include "br1cossres.mm"
include "brin.mm"
include "anbi12i.mm"
include "an2anr.mm"
include "bitri.mm"
include "rexbii.mm"
include "syl6bb.mm"
include "syl5bb.mm"

theorem br1cossinres
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cV: class V
  let cW: class W

  disjoint A u
  disjoint B u
  disjoint C u
  disjoint R u
  disjoint S u
  disjoint V u
  disjoint W u
  assert |- ( ( B e. V /\ C e. W ) -> ( B ,~ ( R i^i ( S |` A ) ) C <-> E. u e. A ( ( u S B /\ u R B ) /\ ( u S C /\ u R C ) ) ) )

  proof
    cB
    cC
    cR
    cS
    cA
    cres
    cin
    #
    ccoss
    #
    wbr
    cB
    cC
    cR
    cS
    cin
    #
    cA
    cres
    #
    ccoss
    #
    wbr
    #
    cB
    cV
    wcel
    cC
    cW
    wcel
    wa
    #
    vu
    cv
    #
    cB
    cS
    wbr
    #
    @7
    cB
    cR
    wbr
    #
    wa
    @7
    cC
    cS
    wbr
    #
    @7
    cC
    cR
    wbr
    #
    wa
    wa
    #
    vu
    cA
    wrex
    #
    cB
    cC
    @1
    @4
    @0
    @3
    cR
    cS
    cA
    inres
    cosseqi
    breqi
    @6
    @5
    @7
    cB
    @2
    wbr
    #
    @7
    cC
    @2
    wbr
    #
    wa
    #
    vu
    cA
    wrex
    @13
    vu
    cA
    cB
    cC
    @2
    cV
    cW
    br1cossres
    @16
    @12
    vu
    cA
    @16
    @9
    @8
    wa
    #
    @11
    @10
    wa
    #
    wa
    @12
    @14
    @17
    @15
    @18
    @7
    cB
    cR
    cS
    brin
    @7
    cC
    cR
    cS
    brin
    anbi12i
    @9
    @8
    @11
    @10
    an2anr
    bitri
    rexbii
    syl6bb
    syl5bb
end
