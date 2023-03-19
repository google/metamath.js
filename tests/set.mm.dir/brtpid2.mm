include "cop.mm"
include "ctp.mm"
include "wbr.mm"
include "wcel.mm"
include "opex.mm"
include "tpid2.mm"
include "df-br.mm"
include "mpbir.mm"

theorem brtpid2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- A { C , <. A , B >. , D } B

  proof
    cA
    cB
    cC
    cA
    cB
    cop
    #
    cD
    ctp
    #
    wbr
    @0
    @1
    wcel
    cC
    @0
    cD
    cA
    cB
    opex
    tpid2
    cA
    cB
    @1
    df-br
    mpbir
end
