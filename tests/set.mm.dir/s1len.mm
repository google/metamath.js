include "cs1.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "cid.mm"
include "cop.mm"
include "csn.mm"
include "c1.mm"
include "df-s1.mm"
include "fveq2i.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "opex.mm"
include "hashsng.mm"
include "ax-mp.mm"
include "eqtri.mm"

theorem s1len
  let cA: class A


  assert |- ( # ` <" A "> ) = 1

  proof
    cA
    cs1
    #
    chash
    cfv
    cc0
    cA
    cid
    cfv
    #
    cop
    #
    csn
    #
    chash
    cfv
    #
    c1
    @0
    @3
    chash
    cA
    df-s1
    fveq2i
    @2
    cvv
    wcel
    @4
    c1
    wceq
    cc0
    @1
    opex
    @2
    cvv
    hashsng
    ax-mp
    eqtri
end
