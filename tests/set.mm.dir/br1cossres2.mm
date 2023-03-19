include "wcel.mm"
include "wa.mm"
include "cres.mm"
include "ccoss.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "cec.mm"
include "br1cossres.mm"
include "exanres3.mm"
include "bitr4d.mm"

theorem br1cossres2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cV: class V
  let cW: class W

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint R x
  disjoint V x
  disjoint W x
  assert |- ( ( B e. V /\ C e. W ) -> ( B ,~ ( R |` A ) C <-> E. x e. A ( B e. [ x ] R /\ C e. [ x ] R ) ) )

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
    cA
    cres
    ccoss
    wbr
    vx
    cv
    #
    cB
    cR
    wbr
    @0
    cC
    cR
    wbr
    wa
    vx
    cA
    wrex
    cB
    @0
    cR
    cec
    #
    wcel
    cC
    @1
    wcel
    wa
    vx
    cA
    wrex
    vx
    cA
    cB
    cC
    cR
    cV
    cW
    br1cossres
    vx
    cA
    cB
    cC
    cR
    cR
    cV
    cW
    exanres3
    bitr4d
end
