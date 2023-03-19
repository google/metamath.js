include "wcel.mm"
include "cotp.mm"
include "c2nd.mm"
include "cfv.mm"
include "cop.mm"
include "df-ot.mm"
include "fveq2i.mm"
include "cvv.mm"
include "wceq.mm"
include "opex.mm"
include "op2ndg.mm"
include "mpan.mm"
include "syl5eq.mm"

theorem ot3rdg
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( C e. V -> ( 2nd ` <. A , B , C >. ) = C )

  proof
    cC
    cV
    wcel
    #
    cA
    cB
    cC
    cotp
    #
    c2nd
    cfv
    cA
    cB
    cop
    #
    cC
    cop
    #
    c2nd
    cfv
    #
    cC
    @1
    @3
    c2nd
    cA
    cB
    cC
    df-ot
    fveq2i
    @2
    cvv
    wcel
    @0
    @4
    cC
    wceq
    cA
    cB
    opex
    @2
    cC
    cvv
    cV
    op2ndg
    mpan
    syl5eq
end
