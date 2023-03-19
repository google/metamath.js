include "cop.mm"
include "csn.mm"
include "ccnv.mm"
include "cint.mm"
include "cnvsn.mm"
include "inteqi.mm"
include "opex.mm"
include "intsn.mm"
include "eqtri.mm"
include "op1stb.mm"

theorem op2ndb
  let cA: class A
  let cB: class B
  assume cnvsn.1: |- A e. _V
  assume cnvsn.2: |- B e. _V


  assert |- |^| |^| |^| `' { <. A , B >. } = B

  proof
    cA
    cB
    cop
    csn
    ccnv
    #
    cint
    #
    cint
    #
    cint
    cB
    cA
    cop
    #
    cint
    #
    cint
    cB
    @2
    @4
    @1
    @3
    @1
    @3
    csn
    #
    cint
    @3
    @0
    @5
    cA
    cB
    cnvsn.1
    cnvsn.2
    cnvsn
    inteqi
    @3
    cB
    cA
    opex
    intsn
    eqtri
    inteqi
    inteqi
    cB
    cA
    cnvsn.2
    cnvsn.1
    op1stb
    eqtri
end
