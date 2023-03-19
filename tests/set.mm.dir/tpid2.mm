include "ctp.mm"
include "wcel.mm"
include "wceq.mm"
include "w3o.mm"
include "eqid.mm"
include "3mix2i.mm"
include "eltp.mm"
include "mpbir.mm"

theorem tpid2
  let cA: class A
  let cB: class B
  let cC: class C
  assume tpid2.1: |- B e. _V


  assert |- B e. { A , B , C }

  proof
    cB
    cA
    cB
    cC
    ctp
    wcel
    cB
    cA
    wceq
    #
    cB
    cB
    wceq
    #
    cB
    cC
    wceq
    #
    w3o
    @1
    @0
    @2
    cB
    eqid
    3mix2i
    cB
    cA
    cB
    cC
    tpid2.1
    eltp
    mpbir
end
