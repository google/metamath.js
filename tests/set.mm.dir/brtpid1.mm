include "cop.mm"
include "ctp.mm"
include "wbr.mm"
include "wcel.mm"
include "opex.mm"
include "tpid1.mm"
include "df-br.mm"
include "mpbir.mm"

theorem brtpid1
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- A { <. A , B >. , C , D } B

  proof
    cA
    cB
    cA
    cB
    cop
    #
    cC
    cD
    ctp
    #
    wbr
    @0
    @1
    wcel
    @0
    cC
    cD
    cA
    cB
    opex
    tpid1
    cA
    cB
    @1
    df-br
    mpbir
end
