include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "csb.mm"
include "cvv.mm"
include "nfa1.mm"
include "nfcvd.mm"
include "wcel.mm"
include "a1i.mm"
include "nfa2.mm"
include "nfv.mm"
include "nfan.mm"
include "2sp.mm"
include "impl.mm"
include "csbiedf.mm"

theorem csbie2t
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume csbie2t.1: |- A e. _V
  assume csbie2t.2: |- B e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint D x
  disjoint D y
  assert |- ( A. x A. y ( ( x = A /\ y = B ) -> C = D ) -> [_ A / x ]_ [_ B / y ]_ C = D )

  proof
    vx
    cv
    cA
    wceq
    #
    vy
    cv
    cB
    wceq
    #
    wa
    cC
    cD
    wceq
    #
    wi
    #
    vy
    wal
    #
    vx
    wal
    #
    vx
    cA
    vy
    cB
    cC
    csb
    cD
    cvv
    @4
    vx
    nfa1
    @5
    vx
    cD
    nfcvd
    cA
    cvv
    wcel
    @5
    csbie2t.1
    a1i
    @5
    @0
    wa
    #
    vy
    cB
    cC
    cD
    cvv
    @5
    @0
    vy
    @3
    vy
    vx
    nfa2
    @0
    vy
    nfv
    nfan
    @6
    vy
    cD
    nfcvd
    cB
    cvv
    wcel
    @6
    csbie2t.2
    a1i
    @5
    @0
    @1
    @2
    @3
    vx
    vy
    2sp
    impl
    csbiedf
    csbiedf
end
