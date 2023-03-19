include "cop.mm"
include "ctp.mm"
include "wbr.mm"
include "wcel.mm"
include "opex.mm"
include "tpid3.mm"
include "df-br.mm"
include "mpbir.mm"

theorem brtpid3
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- A { C , D , <. A , B >. } B

  proof
    cA
    cB
    cC
    cD
    cA
    cB
    cop
    #
    ctp
    #
    wbr
    @0
    @1
    wcel
    cC
    cD
    @0
    cA
    cB
    opex
    tpid3
    cA
    cB
    @1
    df-br
    mpbir
end
