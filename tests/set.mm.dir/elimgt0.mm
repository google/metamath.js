include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cif.mm"
include "breq2.mm"
include "0lt1.mm"
include "elimhyp.mm"

theorem elimgt0
  let cA: class A


  assert |- 0 < if ( 0 < A , A , 1 )

  proof
    cc0
    cA
    clt
    wbr
    #
    cc0
    @0
    cA
    c1
    cif
    #
    clt
    wbr
    cc0
    c1
    clt
    wbr
    cA
    c1
    cA
    @1
    cc0
    clt
    breq2
    c1
    @1
    cc0
    clt
    breq2
    0lt1
    elimhyp
end
