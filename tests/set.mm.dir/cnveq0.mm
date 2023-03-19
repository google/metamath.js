include "c0.mm"
include "ccnv.mm"
include "wceq.mm"
include "wrel.mm"
include "wb.mm"
include "wi.mm"
include "cnv0.mm"
include "rel0.mm"
include "cnveqb.mm"
include "mpan2.mm"
include "eqeq2.mm"
include "bibi2d.mm"
include "syl5ibr.mm"
include "eqcoms.mm"
include "ax-mp.mm"

theorem cnveq0
  let cA: class A


  assert |- ( Rel A -> ( A = (/) <-> `' A = (/) ) )

  proof
    c0
    ccnv
    #
    c0
    wceq
    cA
    wrel
    #
    cA
    c0
    wceq
    #
    cA
    ccnv
    #
    c0
    wceq
    #
    wb
    #
    wi
    #
    cnv0
    @6
    c0
    @0
    @1
    @5
    c0
    @0
    wceq
    #
    @2
    @3
    @0
    wceq
    #
    wb
    #
    @1
    c0
    wrel
    @9
    rel0
    cA
    c0
    cnveqb
    mpan2
    @7
    @4
    @8
    @2
    c0
    @0
    @3
    eqeq2
    bibi2d
    syl5ibr
    eqcoms
    ax-mp
end
