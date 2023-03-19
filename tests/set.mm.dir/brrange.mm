include "c2nd.mm"
include "cvv.mm"
include "cxp.mm"
include "cres.mm"
include "cimage.mm"
include "wbr.mm"
include "cima.mm"
include "wceq.mm"
include "crange.mm"
include "crn.mm"
include "brimage.mm"
include "df-range.mm"
include "breqi.mm"
include "dfrn5.mm"
include "eqeq2i.mm"
include "3bitr4i.mm"

theorem brrange
  let cA: class A
  let cB: class B
  assume brdomain.1: |- A e. _V
  assume brdomain.2: |- B e. _V


  assert |- ( A Range B <-> B = ran A )

  proof
    cA
    cB
    c2nd
    cvv
    cvv
    cxp
    cres
    #
    cimage
    #
    wbr
    cB
    @0
    cA
    cima
    #
    wceq
    cA
    cB
    crange
    wbr
    cB
    cA
    crn
    #
    wceq
    cA
    cB
    @0
    brdomain.1
    brdomain.2
    brimage
    cA
    cB
    crange
    @1
    df-range
    breqi
    @3
    @2
    cB
    cA
    dfrn5
    eqeq2i
    3bitr4i
end
