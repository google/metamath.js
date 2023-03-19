include "cch.mm"
include "wcel.mm"
include "csh.mm"
include "c0h.mm"
include "wss.mm"
include "wceq.mm"
include "wb.mm"
include "chsh.mm"
include "shle0.mm"
include "syl.mm"

theorem chle0
  let cA: class A


  assert |- ( A e. CH -> ( A C_ 0H <-> A = 0H ) )

  proof
    cA
    cch
    wcel
    cA
    csh
    wcel
    cA
    c0h
    wss
    cA
    c0h
    wceq
    wb
    cA
    chsh
    cA
    shle0
    syl
end
