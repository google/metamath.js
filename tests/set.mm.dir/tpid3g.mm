include "wcel.mm"
include "ctp.mm"
include "wceq.mm"
include "w3o.mm"
include "eqid.mm"
include "3mix3i.mm"
include "eltpg.mm"
include "mpbiri.mm"

theorem tpid3g
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A e. B -> A e. { C , D , A } )

  proof
    cA
    cB
    wcel
    cA
    cC
    cD
    cA
    ctp
    wcel
    cA
    cC
    wceq
    #
    cA
    cD
    wceq
    #
    cA
    cA
    wceq
    #
    w3o
    @2
    @0
    @1
    cA
    eqid
    3mix3i
    cA
    cC
    cD
    cA
    cB
    eltpg
    mpbiri
end
