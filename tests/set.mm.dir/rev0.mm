include "c0.mm"
include "creverse.mm"
include "cfv.mm"
include "chash.mm"
include "cc0.mm"
include "wceq.mm"
include "cvv.mm"
include "cword.mm"
include "wcel.mm"
include "wrd0.mm"
include "revlen.mm"
include "ax-mp.mm"
include "hash0.mm"
include "eqtri.mm"
include "wb.mm"
include "fvex.mm"
include "hasheq0.mm"
include "mpbi.mm"

theorem rev0
  let vw: setvar w
  let vx: setvar x
  let cW: class W
  let cA: class A
  let cX: class X


  assert |- ( reverse ` (/) ) = (/)

  proof
    c0
    creverse
    cfv
    #
    chash
    cfv
    #
    cc0
    wceq
    #
    @0
    c0
    wceq
    #
    @1
    c0
    chash
    cfv
    #
    cc0
    c0
    cvv
    cword
    wcel
    @1
    @4
    wceq
    cvv
    wrd0
    cvv
    c0
    revlen
    ax-mp
    hash0
    eqtri
    @0
    cvv
    wcel
    @2
    @3
    wb
    c0
    creverse
    fvex
    @0
    cvv
    hasheq0
    ax-mp
    mpbi
end
