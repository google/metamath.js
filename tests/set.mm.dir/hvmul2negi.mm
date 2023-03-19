include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "csm.mm"
include "mul2negi.mm"
include "oveq1i.mm"
include "negcli.mm"
include "hvmulassi.mm"
include "3eqtr3i.mm"

theorem hvmul2negi
  let cA: class A
  let cB: class B
  let cC: class C
  assume hvmulcom.1: |- A e. CC
  assume hvmulcom.2: |- B e. CC
  assume hvmulcom.3: |- C e. ~H


  assert |- ( -u A .h ( -u B .h C ) ) = ( A .h ( B .h C ) )

  proof
    cA
    cneg
    #
    cB
    cneg
    #
    cmul
    co
    #
    cC
    csm
    co
    cA
    cB
    cmul
    co
    #
    cC
    csm
    co
    @0
    @1
    cC
    csm
    co
    csm
    co
    cA
    cB
    cC
    csm
    co
    csm
    co
    @2
    @3
    cC
    csm
    cA
    cB
    hvmulcom.1
    hvmulcom.2
    mul2negi
    oveq1i
    @0
    @1
    cC
    cA
    hvmulcom.1
    negcli
    cB
    hvmulcom.2
    negcli
    hvmulcom.3
    hvmulassi
    cA
    cB
    cC
    hvmulcom.1
    hvmulcom.2
    hvmulcom.3
    hvmulassi
    3eqtr3i
end
