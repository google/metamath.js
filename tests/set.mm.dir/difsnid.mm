include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "cun.mm"
include "uncom.mm"
include "wss.mm"
include "wceq.mm"
include "snssi.mm"
include "undif.mm"
include "sylib.mm"
include "syl5eq.mm"

theorem difsnid
  let cA: class A
  let cB: class B


  assert |- ( B e. A -> ( ( A \ { B } ) u. { B } ) = A )

  proof
    cB
    cA
    wcel
    #
    cA
    cB
    csn
    #
    cdif
    #
    @1
    cun
    @1
    @2
    cun
    #
    cA
    @2
    @1
    uncom
    @0
    @1
    cA
    wss
    @3
    cA
    wceq
    cB
    cA
    snssi
    @1
    cA
    undif
    sylib
    syl5eq
end
