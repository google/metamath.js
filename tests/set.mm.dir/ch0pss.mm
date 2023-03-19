include "cch.mm"
include "wcel.mm"
include "c0h.mm"
include "wne.mm"
include "wss.mm"
include "wa.mm"
include "wpss.mm"
include "necom.mm"
include "ch0le.mm"
include "biantrurd.mm"
include "syl5bbr.mm"
include "df-pss.mm"
include "syl6rbbr.mm"

theorem ch0pss
  let cA: class A


  assert |- ( A e. CH -> ( 0H C. A <-> A =/= 0H ) )

  proof
    cA
    cch
    wcel
    #
    cA
    c0h
    wne
    #
    c0h
    cA
    wss
    #
    c0h
    cA
    wne
    #
    wa
    #
    c0h
    cA
    wpss
    @1
    @3
    @0
    @4
    c0h
    cA
    necom
    @0
    @2
    @3
    cA
    ch0le
    biantrurd
    syl5bbr
    c0h
    cA
    df-pss
    syl6rbbr
end
