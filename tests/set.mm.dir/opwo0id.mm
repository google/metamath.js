include "cop.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cin.mm"
include "wceq.mm"
include "wcel.mm"
include "wn.mm"
include "0nelop.mm"
include "disjsn.mm"
include "mpbir.mm"
include "disjdif2.mm"
include "ax-mp.mm"
include "eqcomi.mm"

theorem opwo0id
  let cX: class X
  let cY: class Y


  assert |- <. X , Y >. = ( <. X , Y >. \ { (/) } )

  proof
    cX
    cY
    cop
    #
    c0
    csn
    #
    cdif
    #
    @0
    @0
    @1
    cin
    c0
    wceq
    #
    @2
    @0
    wceq
    @3
    c0
    @0
    wcel
    wn
    cX
    cY
    0nelop
    @0
    c0
    disjsn
    mpbir
    @0
    @1
    disjdif2
    ax-mp
    eqcomi
end
