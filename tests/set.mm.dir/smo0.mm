include "cid.mm"
include "c0.mm"
include "cres.mm"
include "wsmo.mm"
include "ord0.mm"
include "iordsmo.mm"
include "wceq.mm"
include "wb.mm"
include "res0.mm"
include "smoeq.mm"
include "ax-mp.mm"
include "mpbi.mm"

theorem smo0
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- Smo (/)

  proof
    cid
    c0
    cres
    #
    wsmo
    #
    c0
    wsmo
    #
    c0
    ord0
    iordsmo
    @0
    c0
    wceq
    @1
    @2
    wb
    cid
    res0
    @0
    c0
    smoeq
    ax-mp
    mpbi
end
