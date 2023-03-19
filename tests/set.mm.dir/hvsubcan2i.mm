include "cva.mm"
include "co.mm"
include "cmv.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "c2.mm"
include "hvsubvali.mm"
include "oveq2i.mm"
include "c0v.mm"
include "neg1cn.mm"
include "hvmulcli.mm"
include "hvadd4i.mm"
include "chil.mm"
include "wcel.mm"
include "wceq.mm"
include "hv2times.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "hvnegidi.mm"
include "oveq12i.mm"
include "eqtri.mm"
include "2cn.mm"
include "ax-hvaddid.mm"

theorem hvsubcan2i
  let cA: class A
  let cB: class B
  assume hvnegdi.1: |- A e. ~H
  assume hvnegdi.2: |- B e. ~H


  assert |- ( ( A +h B ) +h ( A -h B ) ) = ( 2 .h A )

  proof
    cA
    cB
    cva
    co
    #
    cA
    cB
    cmv
    co
    #
    cva
    co
    @0
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
    cva
    co
    #
    c2
    cA
    csm
    co
    #
    @1
    @4
    @0
    cva
    cA
    cB
    hvnegdi.1
    hvnegdi.2
    hvsubvali
    oveq2i
    @5
    @6
    c0v
    cva
    co
    #
    @6
    @5
    cA
    cA
    cva
    co
    #
    cB
    @3
    cva
    co
    #
    cva
    co
    @7
    cA
    cB
    cA
    @3
    hvnegdi.1
    hvnegdi.2
    hvnegdi.1
    @2
    cB
    neg1cn
    hvnegdi.2
    hvmulcli
    hvadd4i
    @8
    @6
    @9
    c0v
    cva
    @6
    @8
    cA
    chil
    wcel
    @6
    @8
    wceq
    hvnegdi.1
    cA
    hv2times
    ax-mp
    eqcomi
    cB
    hvnegdi.2
    hvnegidi
    oveq12i
    eqtri
    @6
    chil
    wcel
    @7
    @6
    wceq
    c2
    cA
    2cn
    hvnegdi.1
    hvmulcli
    @6
    ax-hvaddid
    ax-mp
    eqtri
    eqtri
end
