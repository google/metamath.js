include "cin.mm"
include "wne.mm"
include "wss.mm"
include "wa.mm"
include "wn.mm"
include "wpss.mm"
include "inss1.mm"
include "biantrur.mm"
include "df-ss.mm"
include "necon3bbii.mm"
include "df-pss.mm"
include "3bitr4i.mm"

theorem nssinpss
  let cA: class A
  let cB: class B


  assert |- ( -. A C_ B <-> ( A i^i B ) C. A )

  proof
    cA
    cB
    cin
    #
    cA
    wne
    #
    @0
    cA
    wss
    #
    @1
    wa
    cA
    cB
    wss
    #
    wn
    @0
    cA
    wpss
    @2
    @1
    cA
    cB
    inss1
    biantrur
    @3
    @0
    cA
    cA
    cB
    df-ss
    necon3bbii
    @0
    cA
    df-pss
    3bitr4i
end
