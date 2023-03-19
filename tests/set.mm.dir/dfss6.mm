include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wn.mm"
include "wa.mm"
include "wex.mm"
include "dfss2.mm"
include "notnotb.mm"
include "bitri.mm"
include "exanali.mm"
include "xchbinxr.mm"

theorem dfss6
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A C_ B <-> -. E. x ( x e. A /\ -. x e. B ) )

  proof
    cA
    cB
    wss
    #
    vx
    cv
    #
    cA
    wcel
    #
    @1
    cB
    wcel
    #
    wi
    vx
    wal
    #
    wn
    #
    @2
    @3
    wn
    wa
    vx
    wex
    @0
    @4
    @5
    wn
    vx
    cA
    cB
    dfss2
    @4
    notnotb
    bitri
    @2
    @3
    vx
    exanali
    xchbinxr
end
