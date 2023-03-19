include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "ccoss.mm"
include "wbr.mm"
include "cv.mm"
include "wex.mm"
include "cec.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "brcosscnv.mm"
include "ecinn0.mm"
include "bitr4d.mm"

theorem brcosscnv2
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let cW: class W
  let vx: setvar x


  assert |- ( ( A e. V /\ B e. W ) -> ( A ,~ `' R B <-> ( [ A ] R i^i [ B ] R ) =/= (/) ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    cA
    cB
    cR
    ccnv
    ccoss
    wbr
    cA
    vx
    cv
    #
    cR
    wbr
    cB
    @0
    cR
    wbr
    wa
    vx
    wex
    cA
    cR
    cec
    cB
    cR
    cec
    cin
    c0
    wne
    vx
    cA
    cB
    cR
    cV
    cW
    brcosscnv
    vx
    cA
    cB
    cR
    cV
    cW
    ecinn0
    bitr4d
end
