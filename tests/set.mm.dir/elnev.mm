include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "wn.mm"
include "cab.mm"
include "wne.mm"
include "isset.mm"
include "df-v.mm"
include "eqeq2i.mm"
include "wal.mm"
include "wb.mm"
include "equid.mm"
include "tbt.mm"
include "albii.mm"
include "alnex.mm"
include "abbi.mm"
include "3bitr3ri.mm"
include "bitri.mm"
include "necon2abii.mm"

theorem elnev
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. _V <-> { x | -. x = A } =/= _V )

  proof
    cA
    cvv
    wcel
    vx
    cv
    #
    cA
    wceq
    #
    vx
    wex
    #
    @1
    wn
    #
    vx
    cab
    #
    cvv
    wne
    vx
    cA
    isset
    @2
    @4
    cvv
    @4
    cvv
    wceq
    @4
    @0
    @0
    wceq
    #
    vx
    cab
    #
    wceq
    #
    @2
    wn
    #
    cvv
    @6
    @4
    vx
    df-v
    eqeq2i
    @3
    vx
    wal
    @3
    @5
    wb
    #
    vx
    wal
    @8
    @7
    @3
    @9
    vx
    @5
    @3
    vx
    equid
    tbt
    albii
    @1
    vx
    alnex
    @3
    @5
    vx
    abbi
    3bitr3ri
    bitri
    necon2abii
    bitri
end
