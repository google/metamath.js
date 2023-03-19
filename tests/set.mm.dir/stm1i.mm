include "cst.mm"
include "wcel.mm"
include "cin.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "wss.mm"
include "inss1.mm"
include "chincli.mm"
include "stlei.mm"
include "mpi.mm"
include "breq1.mm"
include "syl5ibcom.mm"
include "stge1i.mm"
include "sylibd.mm"

theorem stm1i
  let cA: class A
  let cB: class B
  let cS: class S
  assume stle.1: |- A e. CH
  assume stle.2: |- B e. CH


  assert |- ( S e. States -> ( ( S ` ( A i^i B ) ) = 1 -> ( S ` A ) = 1 ) )

  proof
    cS
    cst
    wcel
    #
    cA
    cB
    cin
    #
    cS
    cfv
    #
    c1
    wceq
    #
    c1
    cA
    cS
    cfv
    #
    cle
    wbr
    #
    @4
    c1
    wceq
    @0
    @2
    @4
    cle
    wbr
    #
    @3
    @5
    @0
    @1
    cA
    wss
    @6
    cA
    cB
    inss1
    @1
    cA
    cS
    cA
    cB
    stle.1
    stle.2
    chincli
    stle.1
    stlei
    mpi
    @2
    c1
    @4
    cle
    breq1
    syl5ibcom
    cA
    cS
    stle.1
    stge1i
    sylibd
end
