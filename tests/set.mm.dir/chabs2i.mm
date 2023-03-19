include "cch.mm"
include "wcel.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "chabs2.mm"
include "mp2an.mm"

theorem chabs2i
  let cA: class A
  let cB: class B
  assume chabs.1: |- A e. CH
  assume chabs.2: |- B e. CH


  assert |- ( A i^i ( A vH B ) ) = A

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
    chj
    co
    cin
    cA
    wceq
    chabs.1
    chabs.2
    cA
    cB
    chabs2
    mp2an
end
