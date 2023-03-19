include "csh.mm"
include "wcel.mm"
include "cch.mm"
include "wss.mm"
include "wa.mm"
include "chj.mm"
include "co.mm"
include "wb.mm"
include "shlub.mm"
include "mp3an.mm"

theorem shlubi
  let cA: class A
  let cB: class B
  let cC: class C
  assume shlub.1: |- A e. SH
  assume shlub.2: |- B e. SH
  assume shlub.3: |- C e. CH


  assert |- ( ( A C_ C /\ B C_ C ) <-> ( A vH B ) C_ C )

  proof
    cA
    csh
    wcel
    cB
    csh
    wcel
    cC
    cch
    wcel
    cA
    cC
    wss
    cB
    cC
    wss
    wa
    cA
    cB
    chj
    co
    cC
    wss
    wb
    shlub.1
    shlub.2
    shlub.3
    cA
    cB
    cC
    shlub
    mp3an
end
