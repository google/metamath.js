include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "cif.mm"
include "neeq1.mm"
include "ax-1ne0.mm"
include "elimhyp.mm"

theorem elimne0
  let cA: class A


  assert |- if ( A =/= 0 , A , 1 ) =/= 0

  proof
    cA
    cc0
    wne
    #
    @0
    cA
    c1
    cif
    #
    cc0
    wne
    c1
    cc0
    wne
    cA
    c1
    cA
    @1
    cc0
    neeq1
    c1
    @1
    cc0
    neeq1
    ax-1ne0
    elimhyp
end
