include "cva.mm"
include "co.mm"
include "wceq.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "oveq1.mm"
include "c0v.mm"
include "neg1cn.mm"
include "hvmulcli.mm"
include "hvadd32i.mm"
include "hvnegidi.mm"
include "oveq1i.mm"
include "hvaddid2i.mm"
include "3eqtri.mm"
include "3eqtr3g.mm"
include "oveq2.mm"
include "impbii.mm"

theorem hvaddcani
  let cA: class A
  let cB: class B
  let cC: class C
  assume hvnegdi.1: |- A e. ~H
  assume hvnegdi.2: |- B e. ~H
  assume hvaddcan.3: |- C e. ~H


  assert |- ( ( A +h B ) = ( A +h C ) <-> B = C )

  proof
    cA
    cB
    cva
    co
    #
    cA
    cC
    cva
    co
    #
    wceq
    #
    cB
    cC
    wceq
    @2
    @0
    c1
    cneg
    #
    cA
    csm
    co
    #
    cva
    co
    #
    @1
    @4
    cva
    co
    #
    cB
    cC
    @0
    @1
    @4
    cva
    oveq1
    @5
    cA
    @4
    cva
    co
    #
    cB
    cva
    co
    c0v
    cB
    cva
    co
    cB
    cA
    cB
    @4
    hvnegdi.1
    hvnegdi.2
    @3
    cA
    neg1cn
    hvnegdi.1
    hvmulcli
    #
    hvadd32i
    @7
    c0v
    cB
    cva
    cA
    hvnegdi.1
    hvnegidi
    #
    oveq1i
    cB
    hvnegdi.2
    hvaddid2i
    3eqtri
    @6
    @7
    cC
    cva
    co
    c0v
    cC
    cva
    co
    cC
    cA
    cC
    @4
    hvnegdi.1
    hvaddcan.3
    @8
    hvadd32i
    @7
    c0v
    cC
    cva
    @9
    oveq1i
    cC
    hvaddcan.3
    hvaddid2i
    3eqtri
    3eqtr3g
    cB
    cC
    cA
    cva
    oveq2
    impbii
end
