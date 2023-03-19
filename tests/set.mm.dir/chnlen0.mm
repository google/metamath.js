include "cch.mm"
include "wcel.mm"
include "c0h.mm"
include "wceq.mm"
include "wss.mm"
include "ch0le.mm"
include "sseq1.mm"
include "syl5ibrcom.mm"
include "con3d.mm"

theorem chnlen0
  let cA: class A
  let cB: class B


  assert |- ( B e. CH -> ( -. A C_ B -> -. A = 0H ) )

  proof
    cB
    cch
    wcel
    #
    cA
    c0h
    wceq
    #
    cA
    cB
    wss
    #
    @0
    @2
    @1
    c0h
    cB
    wss
    cB
    ch0le
    cA
    c0h
    cB
    sseq1
    syl5ibrcom
    con3d
end
