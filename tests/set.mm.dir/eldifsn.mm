include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "wne.mm"
include "eldif.mm"
include "elsng.mm"
include "necon3bbid.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem eldifsn
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. ( B \ { C } ) <-> ( A e. B /\ A =/= C ) )

  proof
    cA
    cB
    cC
    csn
    #
    cdif
    wcel
    cA
    cB
    wcel
    #
    cA
    @0
    wcel
    #
    wn
    #
    wa
    @1
    cA
    cC
    wne
    #
    wa
    cA
    cB
    @0
    eldif
    @1
    @3
    @4
    @1
    @2
    cA
    cC
    cA
    cC
    cB
    elsng
    necon3bbid
    pm5.32i
    bitri
end
