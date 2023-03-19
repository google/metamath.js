include "wcel.mm"
include "ctp.mm"
include "wceq.mm"
include "w3o.mm"
include "eqid.mm"
include "3mix1i.mm"
include "eltpg.mm"
include "mpbiri.mm"

theorem tpid1g
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A e. B -> A e. { A , C , D } )

  proof
    cA
    cB
    wcel
    cA
    cA
    cC
    cD
    ctp
    wcel
    cA
    cA
    wceq
    #
    cA
    cC
    wceq
    #
    cA
    cD
    wceq
    #
    w3o
    @0
    @1
    @2
    cA
    eqid
    3mix1i
    cA
    cA
    cC
    cD
    cB
    eltpg
    mpbiri
end
