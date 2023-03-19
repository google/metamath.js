include "cvtx.mm"
include "cfv.mm"
include "wceq.mm"
include "ciedg.mm"
include "cop.mm"
include "fveq2i.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "opvtxfv.mm"
include "mp2an.mm"
include "eqtr2i.mm"
include "opiedgfv.mm"
include "pm3.2i.mm"

theorem graop
  let cG: class G
  let cH: class H
  assume graop.h: |- H = <. ( Vtx ` G ) , ( iEdg ` G ) >.


  assert |- ( ( Vtx ` G ) = ( Vtx ` H ) /\ ( iEdg ` G ) = ( iEdg ` H ) )

  proof
    cG
    cvtx
    cfv
    #
    cH
    cvtx
    cfv
    #
    wceq
    cG
    ciedg
    cfv
    #
    cH
    ciedg
    cfv
    #
    wceq
    @1
    @0
    @2
    cop
    #
    cvtx
    cfv
    #
    @0
    cH
    @4
    cvtx
    graop.h
    fveq2i
    @0
    cvv
    wcel
    #
    @2
    cvv
    wcel
    #
    @5
    @0
    wceq
    cG
    cvtx
    fvex
    #
    cG
    ciedg
    fvex
    #
    @2
    @0
    cvv
    cvv
    opvtxfv
    mp2an
    eqtr2i
    @3
    @4
    ciedg
    cfv
    #
    @2
    cH
    @4
    ciedg
    graop.h
    fveq2i
    @6
    @7
    @10
    @2
    wceq
    @8
    @9
    @2
    @0
    cvv
    cvv
    opiedgfv
    mp2an
    eqtr2i
    pm3.2i
end
