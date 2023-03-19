include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "wcel.mm"
include "cio.mm"
include "cab.mm"
include "csingles.mm"
include "cin.mm"
include "cuni.mm"
include "dffv3.mm"
include "dfiota3.mm"
include "abid2.mm"
include "sneqi.mm"
include "ineq1i.mm"
include "unieqi.mm"
include "3eqtri.mm"

theorem dffv5
  let cA: class A
  let cF: class F
  let vx: setvar x


  assert |- ( F ` A ) = U. U. ( { ( F " { A } ) } i^i Singletons )

  proof
    cA
    cF
    cfv
    vx
    cv
    cF
    cA
    csn
    cima
    #
    wcel
    #
    vx
    cio
    @1
    vx
    cab
    #
    csn
    #
    csingles
    cin
    #
    cuni
    #
    cuni
    @0
    csn
    #
    csingles
    cin
    #
    cuni
    #
    cuni
    vx
    cA
    cF
    dffv3
    @1
    vx
    dfiota3
    @5
    @8
    @4
    @7
    @3
    @6
    csingles
    @2
    @0
    vx
    @0
    abid2
    sneqi
    ineq1i
    unieqi
    unieqi
    3eqtri
end
