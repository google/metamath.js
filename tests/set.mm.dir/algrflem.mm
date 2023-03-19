include "c1st.mm"
include "ccom.mm"
include "co.mm"
include "cop.mm"
include "cfv.mm"
include "df-ov.mm"
include "cvv.mm"
include "wf.mm"
include "wcel.mm"
include "wceq.mm"
include "wfo.mm"
include "fo1st.mm"
include "fof.mm"
include "ax-mp.mm"
include "opex.mm"
include "fvco3.mm"
include "mp2an.mm"
include "op1st.mm"
include "fveq2i.mm"
include "3eqtri.mm"

theorem algrflem
  let cB: class B
  let cC: class C
  let cF: class F
  assume algrflem.1: |- B e. _V
  assume algrflem.2: |- C e. _V


  assert |- ( B ( F o. 1st ) C ) = ( F ` B )

  proof
    cB
    cC
    cF
    c1st
    ccom
    #
    co
    cB
    cC
    cop
    #
    @0
    cfv
    #
    @1
    c1st
    cfv
    #
    cF
    cfv
    #
    cB
    cF
    cfv
    cB
    cC
    @0
    df-ov
    cvv
    cvv
    c1st
    wf
    #
    @1
    cvv
    wcel
    @2
    @4
    wceq
    cvv
    cvv
    c1st
    wfo
    @5
    fo1st
    cvv
    cvv
    c1st
    fof
    ax-mp
    cB
    cC
    opex
    cvv
    cvv
    @1
    cF
    c1st
    fvco3
    mp2an
    @3
    cB
    cF
    cB
    cC
    algrflem.1
    algrflem.2
    op1st
    fveq2i
    3eqtri
end
