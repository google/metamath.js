include "wcel.mm"
include "cotp.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "wceq.mm"
include "wa.mm"
include "cop.mm"
include "df-ot.mm"
include "fveq2i.mm"
include "cvv.mm"
include "opex.mm"
include "op1stg.mm"
include "mpan.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "op2ndg.mm"
include "sylan9eqr.mm"
include "3impa.mm"

theorem ot2ndg
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( 2nd ` ( 1st ` <. A , B , C >. ) ) = B )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    cC
    cX
    wcel
    #
    cA
    cB
    cC
    cotp
    #
    c1st
    cfv
    #
    c2nd
    cfv
    #
    cB
    wceq
    @2
    @0
    @1
    wa
    @5
    cA
    cB
    cop
    #
    c2nd
    cfv
    cB
    @2
    @4
    @6
    c2nd
    @2
    @4
    @6
    cC
    cop
    #
    c1st
    cfv
    #
    @6
    @3
    @7
    c1st
    cA
    cB
    cC
    df-ot
    fveq2i
    @6
    cvv
    wcel
    @2
    @8
    @6
    wceq
    cA
    cB
    opex
    @6
    cC
    cvv
    cX
    op1stg
    mpan
    syl5eq
    fveq2d
    cA
    cB
    cV
    cW
    op2ndg
    sylan9eqr
    3impa
end
