include "cvv.mm"
include "cdif.mm"
include "cun.mm"
include "cin.mm"
include "c0.mm"
include "dfun3.mm"
include "disjdif.mm"
include "difeq2i.mm"
include "dif0.mm"
include "3eqtri.mm"

theorem unvdif
  let cA: class A


  assert |- ( A u. ( _V \ A ) ) = _V

  proof
    cA
    cvv
    cA
    cdif
    #
    cun
    cvv
    @0
    cvv
    @0
    cdif
    cin
    #
    cdif
    cvv
    c0
    cdif
    cvv
    cA
    @0
    dfun3
    @1
    c0
    cvv
    @0
    cvv
    disjdif
    difeq2i
    cvv
    dif0
    3eqtri
end
