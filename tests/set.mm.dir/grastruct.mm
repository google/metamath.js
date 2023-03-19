include "cvtx.mm"
include "cfv.mm"
include "wceq.mm"
include "ciedg.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "struct2grvtx.mm"
include "mp2an.mm"
include "eqcomi.mm"
include "struct2griedg.mm"
include "pm3.2i.mm"

theorem grastruct
  let cG: class G
  let cH: class H
  assume grastruct.h: |- H = { <. ( Base ` ndx ) , ( Vtx ` G ) >. , <. ( .ef ` ndx ) , ( iEdg ` G ) >. }


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
    @0
    cvv
    wcel
    #
    @2
    cvv
    wcel
    #
    @1
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
    cH
    @0
    cvv
    cvv
    grastruct.h
    struct2grvtx
    mp2an
    eqcomi
    @3
    @2
    @4
    @5
    @3
    @2
    wceq
    @6
    @7
    @2
    cH
    @0
    cvv
    cvv
    grastruct.h
    struct2griedg
    mp2an
    eqcomi
    pm3.2i
end
