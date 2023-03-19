include "cmv.mm"
include "co.mm"
include "wceq.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "cva.mm"
include "hvsubvali.mm"
include "eqeq1i.mm"
include "c0v.mm"
include "neg1cn.mm"
include "hvmulcli.mm"
include "hvadd12i.mm"
include "hvnegidi.mm"
include "oveq2i.mm"
include "chil.mm"
include "wcel.mm"
include "ax-hvaddid.mm"
include "ax-mp.mm"
include "3eqtri.mm"
include "hvaddcli.mm"
include "hvaddcani.mm"
include "eqcom.mm"
include "3bitr3i.mm"
include "bitri.mm"

theorem hvsubaddi
  let cA: class A
  let cB: class B
  let cC: class C
  assume hvnegdi.1: |- A e. ~H
  assume hvnegdi.2: |- B e. ~H
  assume hvaddcan.3: |- C e. ~H


  assert |- ( ( A -h B ) = C <-> ( B +h C ) = A )

  proof
    cA
    cB
    cmv
    co
    #
    cC
    wceq
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
    wceq
    #
    cB
    cC
    cva
    co
    #
    cA
    wceq
    #
    @0
    @3
    cC
    cA
    cB
    hvnegdi.1
    hvnegdi.2
    hvsubvali
    eqeq1i
    cB
    @3
    cva
    co
    #
    @5
    wceq
    cA
    @5
    wceq
    @4
    @6
    @7
    cA
    @5
    @7
    cA
    cB
    @2
    cva
    co
    #
    cva
    co
    cA
    c0v
    cva
    co
    #
    cA
    cB
    cA
    @2
    hvnegdi.2
    hvnegdi.1
    @1
    cB
    neg1cn
    hvnegdi.2
    hvmulcli
    #
    hvadd12i
    @8
    c0v
    cA
    cva
    cB
    hvnegdi.2
    hvnegidi
    oveq2i
    cA
    chil
    wcel
    @9
    cA
    wceq
    hvnegdi.1
    cA
    ax-hvaddid
    ax-mp
    3eqtri
    eqeq1i
    cB
    @3
    cC
    hvnegdi.2
    cA
    @2
    hvnegdi.1
    @10
    hvaddcli
    hvaddcan.3
    hvaddcani
    cA
    @5
    eqcom
    3bitr3i
    bitri
end
