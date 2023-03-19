include "cv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cres.mm"
include "wceq.mm"
include "cfv.mm"
include "fveq1.mm"
include "wcel.mm"
include "fvres.mm"
include "ax-mp.mm"
include "syl6eq.mm"

theorem jm2.27dlem1
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  assume jm2.27dlem1.1: |- A e. ( 1 ... B )

  disjoint A a
  disjoint A b
  disjoint a b
  disjoint B a
  disjoint B b
  assert |- ( a = ( b |` ( 1 ... B ) ) -> ( a ` A ) = ( b ` A ) )

  proof
    va
    cv
    #
    vb
    cv
    #
    c1
    cB
    cfz
    co
    #
    cres
    #
    wceq
    cA
    @0
    cfv
    cA
    @3
    cfv
    #
    cA
    @1
    cfv
    #
    cA
    @0
    @3
    fveq1
    cA
    @2
    wcel
    @4
    @5
    wceq
    jm2.27dlem1.1
    cA
    @2
    @1
    fvres
    ax-mp
    syl6eq
end
