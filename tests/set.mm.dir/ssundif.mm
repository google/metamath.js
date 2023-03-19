include "cv.mm"
include "wcel.mm"
include "cun.mm"
include "wi.mm"
include "wal.mm"
include "cdif.mm"
include "wss.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "pm5.6.mm"
include "eldif.mm"
include "imbi1i.mm"
include "elun.mm"
include "imbi2i.mm"
include "3bitr4ri.mm"
include "albii.mm"
include "dfss2.mm"
include "3bitr4i.mm"

theorem ssundif
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A C_ ( B u. C ) <-> ( A \ B ) C_ C )

  proof
    vx
    cv
    #
    cA
    wcel
    #
    @0
    cB
    cC
    cun
    #
    wcel
    #
    wi
    #
    vx
    wal
    @0
    cA
    cB
    cdif
    #
    wcel
    #
    @0
    cC
    wcel
    #
    wi
    #
    vx
    wal
    cA
    @2
    wss
    @5
    cC
    wss
    @4
    @8
    vx
    @1
    @0
    cB
    wcel
    #
    wn
    wa
    #
    @7
    wi
    @1
    @9
    @7
    wo
    #
    wi
    @8
    @4
    @1
    @9
    @7
    pm5.6
    @6
    @10
    @7
    @0
    cA
    cB
    eldif
    imbi1i
    @3
    @11
    @1
    @0
    cB
    cC
    elun
    imbi2i
    3bitr4ri
    albii
    vx
    cA
    @2
    dfss2
    vx
    @5
    cC
    dfss2
    3bitr4i
end
