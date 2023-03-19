include "wcel.mm"
include "cin.mm"
include "crest.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "eqid.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "elrest.mm"
include "syl5ibr.mm"
include "3impia.mm"

theorem elrestr
  let cA: class A
  let cS: class S
  let cJ: class J
  let cV: class V
  let cW: class W
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( ( J e. V /\ S e. W /\ A e. J ) -> ( A i^i S ) e. ( J |`t S ) )

  proof
    cJ
    cV
    wcel
    #
    cS
    cW
    wcel
    #
    cA
    cJ
    wcel
    #
    cA
    cS
    cin
    #
    cJ
    cS
    crest
    co
    wcel
    #
    @2
    @4
    @0
    @1
    wa
    @3
    vx
    cv
    #
    cS
    cin
    #
    wceq
    #
    vx
    cJ
    wrex
    #
    @2
    @3
    @3
    wceq
    #
    @8
    @3
    eqid
    @7
    @9
    vx
    cA
    cJ
    @5
    cA
    wceq
    @6
    @3
    @3
    @5
    cA
    cS
    ineq1
    eqeq2d
    rspcev
    mpan2
    vx
    @3
    cS
    cJ
    cV
    cW
    elrest
    syl5ibr
    3impia
end
