include "cin.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cst.mm"
include "wcel.mm"
include "incom.mm"
include "fveq2i.mm"
include "eqeq1i.mm"
include "stm1i.mm"
include "syl5bi.mm"

theorem stm1ri
  let cA: class A
  let cB: class B
  let cS: class S
  assume stle.1: |- A e. CH
  assume stle.2: |- B e. CH


  assert |- ( S e. States -> ( ( S ` ( A i^i B ) ) = 1 -> ( S ` B ) = 1 ) )

  proof
    cA
    cB
    cin
    #
    cS
    cfv
    #
    c1
    wceq
    cB
    cA
    cin
    #
    cS
    cfv
    #
    c1
    wceq
    cS
    cst
    wcel
    cB
    cS
    cfv
    c1
    wceq
    @1
    @3
    c1
    @0
    @2
    cS
    cA
    cB
    incom
    fveq2i
    eqeq1i
    cB
    cA
    cS
    stle.2
    stle.1
    stm1i
    syl5bi
end
