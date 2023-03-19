include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "wbr.mm"
include "wceq.mm"
include "wb.mm"
include "cv.mm"
include "wi.mm"
include "breq2.mm"
include "eqeq2.mm"
include "bibi12d.mm"
include "imbi2d.mm"
include "cop.mm"
include "vex.mm"
include "opres.mm"
include "df-br.mm"
include "ideq.mm"
include "bitr3i.mm"
include "3bitr4g.mm"
include "vtoclg.mm"
include "impcom.mm"

theorem resieq
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( ( B e. A /\ C e. A ) -> ( B ( _I |` A ) C <-> B = C ) )

  proof
    cC
    cA
    wcel
    cB
    cA
    wcel
    #
    cB
    cC
    cid
    cA
    cres
    #
    wbr
    #
    cB
    cC
    wceq
    #
    wb
    #
    @0
    cB
    vx
    cv
    #
    @1
    wbr
    #
    cB
    @5
    wceq
    #
    wb
    #
    wi
    @0
    @4
    wi
    vx
    cC
    cA
    @5
    cC
    wceq
    #
    @8
    @4
    @0
    @9
    @6
    @2
    @7
    @3
    @5
    cC
    cB
    @1
    breq2
    @5
    cC
    cB
    eqeq2
    bibi12d
    imbi2d
    @0
    cB
    @5
    cop
    #
    @1
    wcel
    @10
    cid
    wcel
    #
    @6
    @7
    cB
    @5
    cid
    cA
    vx
    vex
    #
    opres
    cB
    @5
    @1
    df-br
    @7
    cB
    @5
    cid
    wbr
    @11
    cB
    @5
    @12
    ideq
    cB
    @5
    cid
    df-br
    bitr3i
    3bitr4g
    vtoclg
    impcom
end
