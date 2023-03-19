include "ctp.mm"
include "wcel.mm"
include "wceq.mm"
include "w3o.mm"
include "eqid.mm"
include "3mix1i.mm"
include "eltp.mm"
include "mpbir.mm"

theorem tpid1
  let cA: class A
  let cB: class B
  let cC: class C
  assume tpid1.1: |- A e. _V


  assert |- A e. { A , B , C }

  proof
    cA
    cA
    cB
    cC
    ctp
    wcel
    cA
    cA
    wceq
    #
    cA
    cB
    wceq
    #
    cA
    cC
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
    cB
    cC
    tpid1.1
    eltp
    mpbir
end
