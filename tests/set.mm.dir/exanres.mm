include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cres.mm"
include "wbr.mm"
include "wex.mm"
include "wrex.mm"
include "brresALTV.mm"
include "bi2anan9.mm"
include "anandi.mm"
include "syl6bbr.mm"
include "exbidv.mm"
include "df-rex.mm"

theorem exanres
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cV: class V
  let cW: class W

  disjoint B u
  disjoint C u
  disjoint V u
  disjoint W u
  assert |- ( ( B e. V /\ C e. W ) -> ( E. u ( u ( R |` A ) B /\ u ( S |` A ) C ) <-> E. u e. A ( u R B /\ u S C ) ) )

  proof
    cB
    cV
    wcel
    #
    cC
    cW
    wcel
    #
    wa
    #
    vu
    cv
    #
    cB
    cR
    cA
    cres
    wbr
    #
    @3
    cC
    cS
    cA
    cres
    wbr
    #
    wa
    #
    vu
    wex
    @3
    cA
    wcel
    #
    @3
    cB
    cR
    wbr
    #
    @3
    cC
    cS
    wbr
    #
    wa
    #
    wa
    #
    vu
    wex
    @10
    vu
    cA
    wrex
    @2
    @6
    @11
    vu
    @2
    @6
    @7
    @8
    wa
    #
    @7
    @9
    wa
    #
    wa
    @11
    @0
    @4
    @12
    @1
    @5
    @13
    cA
    @3
    cB
    cR
    cV
    brresALTV
    cA
    @3
    cC
    cS
    cW
    brresALTV
    bi2anan9
    @7
    @8
    @9
    anandi
    syl6bbr
    exbidv
    @10
    vu
    cA
    df-rex
    syl6bbr
end
