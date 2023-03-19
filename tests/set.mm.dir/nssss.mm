include "cv.mm"
include "wss.mm"
include "wn.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "exanali.mm"
include "ssextss.mm"
include "xchbinxr.mm"
include "bicomi.mm"

theorem nssss
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( -. A C_ B <-> E. x ( x C_ A /\ -. x C_ B ) )

  proof
    vx
    cv
    #
    cA
    wss
    #
    @0
    cB
    wss
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
    ssextss
    xchbinxr
    bicomi
end
