include "cop.mm"
include "crngo.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "cablo.mm"
include "wbr.mm"
include "wceq.mm"
include "df-br.mm"
include "cvv.mm"
include "wa.mm"
include "wrel.mm"
include "relrngo.mm"
include "brrelex12.mm"
include "mpan.mm"
include "op1stg.mm"
include "syl.mm"
include "sylbir.mm"
include "eqid.mm"
include "rngoablo.mm"
include "eqeltrrd.mm"

theorem rngoablo2
  let cG: class G
  let cH: class H


  assert |- ( <. G , H >. e. RingOps -> G e. AbelOp )

  proof
    cG
    cH
    cop
    #
    crngo
    wcel
    #
    @0
    c1st
    cfv
    #
    cG
    cablo
    @1
    cG
    cH
    crngo
    wbr
    #
    @2
    cG
    wceq
    #
    cG
    cH
    crngo
    df-br
    @3
    cG
    cvv
    wcel
    cH
    cvv
    wcel
    wa
    #
    @4
    crngo
    wrel
    @3
    @5
    relrngo
    cG
    cH
    crngo
    brrelex12
    mpan
    cG
    cH
    cvv
    cvv
    op1stg
    syl
    sylbir
    @0
    @2
    @2
    eqid
    rngoablo
    eqeltrrd
end
