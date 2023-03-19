include "cch.mm"
include "wcel.mm"
include "cin.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "chabs1.mm"
include "mp2an.mm"

theorem chabs1i
  let cA: class A
  let cB: class B
  assume chabs.1: |- A e. CH
  assume chabs.2: |- B e. CH


  assert |- ( A vH ( A i^i B ) ) = A

  proof
    cA
    cch
    wcel
    cB
    cch
    wcel
    cA
    cA
    cB
    cin
    chj
    co
    cA
    wceq
    chabs.1
    chabs.2
    cA
    cB
    chabs1
    mp2an
end
