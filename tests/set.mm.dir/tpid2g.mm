include "wcel.mm"
include "ctp.mm"
include "wceq.mm"
include "w3o.mm"
include "eqid.mm"
include "3mix2i.mm"
include "eltpg.mm"
include "mpbiri.mm"

theorem tpid2g
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A e. B -> A e. { C , A , D } )

  proof
    cA
    cB
    wcel
    cA
    cC
    cA
    cD
    ctp
    wcel
    cA
    cC
    wceq
    #
    cA
    cA
    wceq
    #
    cA
    cD
    wceq
    #
    w3o
    @1
    @0
    @2
    cA
    eqid
    3mix2i
    cA
    cC
    cA
    cD
    cB
    eltpg
    mpbiri
end
