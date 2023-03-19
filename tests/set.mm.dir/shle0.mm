include "csh.mm"
include "wcel.mm"
include "c0h.mm"
include "wss.mm"
include "wa.mm"
include "wceq.mm"
include "sh0le.mm"
include "biantrud.mm"
include "eqss.mm"
include "syl6bbr.mm"

theorem shle0
  let cA: class A


  assert |- ( A e. SH -> ( A C_ 0H <-> A = 0H ) )

  proof
    cA
    csh
    wcel
    #
    cA
    c0h
    wss
    #
    @1
    c0h
    cA
    wss
    #
    wa
    cA
    c0h
    wceq
    @0
    @2
    @1
    cA
    sh0le
    biantrud
    cA
    c0h
    eqss
    syl6bbr
end
