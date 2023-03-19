include "c1st.mm"
include "cvv.mm"
include "cxp.mm"
include "cres.mm"
include "cimage.mm"
include "wbr.mm"
include "cima.mm"
include "wceq.mm"
include "cdomain.mm"
include "cdm.mm"
include "brimage.mm"
include "df-domain.mm"
include "breqi.mm"
include "dfdm5.mm"
include "eqeq2i.mm"
include "3bitr4i.mm"

theorem brdomain
  let cA: class A
  let cB: class B
  assume brdomain.1: |- A e. _V
  assume brdomain.2: |- B e. _V


  assert |- ( A Domain B <-> B = dom A )

  proof
    cA
    cB
    c1st
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
    cdomain
    wbr
    cB
    cA
    cdm
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
    cdomain
    @1
    df-domain
    breqi
    @3
    @2
    cB
    cA
    dfdm5
    eqeq2i
    3bitr4i
end
