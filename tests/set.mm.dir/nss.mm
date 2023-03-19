include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "wex.mm"
include "wss.mm"
include "wi.mm"
include "wal.mm"
include "exanali.mm"
include "dfss2.mm"
include "xchbinxr.mm"
include "bicomi.mm"

theorem nss
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( -. A C_ B <-> E. x ( x e. A /\ -. x e. B ) )

  proof
    vx
    cv
    #
    cA
    wcel
    #
    @0
    cB
    wcel
    #
    wn
    wa
    vx
    wex
    #
    cA
    cB
    wss
    #
    wn
    @3
    @1
    @2
    wi
    vx
    wal
    @4
    @1
    @2
    vx
    exanali
    vx
    cA
    cB
    dfss2
    xchbinxr
    bicomi
end
