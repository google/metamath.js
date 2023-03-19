include "wcel.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "cv.mm"
include "cin.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "wrex.mm"
include "restval.mm"
include "eleq2d.mm"
include "eqid.mm"
include "vex.mm"
include "inex1.mm"
include "elrnmpti.mm"
include "syl6bb.mm"

theorem elrest
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cJ: class J
  let cV: class V
  let cW: class W
  let vj: setvar j
  let vy: setvar y
  let cS: class S

  disjoint A x
  disjoint B x
  disjoint J x
  disjoint j x
  disjoint j y
  disjoint A j
  disjoint x y
  disjoint A y
  disjoint J j
  disjoint J y
  disjoint S x
  assert |- ( ( J e. V /\ B e. W ) -> ( A e. ( J |`t B ) <-> E. x e. J A = ( x i^i B ) ) )

  proof
    cJ
    cV
    wcel
    cB
    cW
    wcel
    wa
    #
    cA
    cJ
    cB
    crest
    co
    #
    wcel
    cA
    vx
    cJ
    vx
    cv
    #
    cB
    cin
    #
    cmpt
    #
    crn
    #
    wcel
    cA
    @3
    wceq
    vx
    cJ
    wrex
    @0
    @1
    @5
    cA
    vx
    cB
    cJ
    cV
    cW
    restval
    eleq2d
    vx
    cJ
    @3
    cA
    @4
    @4
    eqid
    @2
    cB
    vx
    vex
    inex1
    elrnmpti
    syl6bb
end
