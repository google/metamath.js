include "cpr.mm"
include "wceq.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "id.mm"
include "a1i.mm"
include "preq1b.mm"
include "ax-mp.mm"
include "biimpi.mm"

theorem preqr1
  let cA: class A
  let cB: class B
  let cC: class C
  assume preqr1.a: |- A e. _V
  assume preqr1.b: |- B e. _V


  assert |- ( { A , C } = { B , C } -> A = B )

  proof
    cA
    cC
    cpr
    cB
    cC
    cpr
    wceq
    #
    cA
    cB
    wceq
    #
    cA
    cvv
    wcel
    #
    @0
    @1
    wb
    preqr1.a
    @2
    cA
    cB
    cC
    cvv
    cvv
    @2
    id
    cB
    cvv
    wcel
    @2
    preqr1.b
    a1i
    preq1b
    ax-mp
    biimpi
end
