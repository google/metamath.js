include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "cmv.mm"
include "neg1cn.mm"
include "hvmulcli.mm"
include "hvadd4i.mm"
include "hvdistr1i.mm"
include "oveq2i.mm"
include "3eqtr4i.mm"
include "hvaddcli.mm"
include "hvsubvali.mm"
include "oveq12i.mm"

theorem hvsubsub4i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume hvass.1: |- A e. ~H
  assume hvass.2: |- B e. ~H
  assume hvass.3: |- C e. ~H
  assume hvadd4.4: |- D e. ~H


  assert |- ( ( A -h B ) -h ( C -h D ) ) = ( ( A -h C ) -h ( B -h D ) )

  proof
    cA
    c1
    cneg
    #
    cB
    csm
    co
    #
    cva
    co
    #
    cC
    @0
    cD
    csm
    co
    #
    cva
    co
    #
    cmv
    co
    #
    cA
    @0
    cC
    csm
    co
    #
    cva
    co
    #
    cB
    @3
    cva
    co
    #
    cmv
    co
    #
    cA
    cB
    cmv
    co
    #
    cC
    cD
    cmv
    co
    #
    cmv
    co
    cA
    cC
    cmv
    co
    #
    cB
    cD
    cmv
    co
    #
    cmv
    co
    @2
    @0
    @4
    csm
    co
    #
    cva
    co
    #
    @7
    @0
    @8
    csm
    co
    #
    cva
    co
    #
    @5
    @9
    @2
    @6
    @0
    @3
    csm
    co
    #
    cva
    co
    #
    cva
    co
    @7
    @1
    @18
    cva
    co
    #
    cva
    co
    @15
    @17
    cA
    @1
    @6
    @18
    hvass.1
    @0
    cB
    neg1cn
    hvass.2
    hvmulcli
    #
    @0
    cC
    neg1cn
    hvass.3
    hvmulcli
    #
    @0
    @3
    neg1cn
    @0
    cD
    neg1cn
    hvadd4.4
    hvmulcli
    #
    hvmulcli
    hvadd4i
    @14
    @19
    @2
    cva
    @0
    cC
    @3
    neg1cn
    hvass.3
    @23
    hvdistr1i
    oveq2i
    @16
    @20
    @7
    cva
    @0
    cB
    @3
    neg1cn
    hvass.2
    @23
    hvdistr1i
    oveq2i
    3eqtr4i
    @2
    @4
    cA
    @1
    hvass.1
    @21
    hvaddcli
    cC
    @3
    hvass.3
    @23
    hvaddcli
    hvsubvali
    @7
    @8
    cA
    @6
    hvass.1
    @22
    hvaddcli
    cB
    @3
    hvass.2
    @23
    hvaddcli
    hvsubvali
    3eqtr4i
    @10
    @2
    @11
    @4
    cmv
    cA
    cB
    hvass.1
    hvass.2
    hvsubvali
    cC
    cD
    hvass.3
    hvadd4.4
    hvsubvali
    oveq12i
    @12
    @7
    @13
    @8
    cmv
    cA
    cC
    hvass.1
    hvass.3
    hvsubvali
    cB
    cD
    hvass.2
    hvadd4.4
    hvsubvali
    oveq12i
    3eqtr4i
end
