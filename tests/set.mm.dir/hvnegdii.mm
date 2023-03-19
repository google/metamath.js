include "c1.mm"
include "cneg.mm"
include "cmv.mm"
include "co.mm"
include "csm.mm"
include "cva.mm"
include "hvsubvali.mm"
include "oveq2i.mm"
include "neg1cn.mm"
include "hvmulcli.mm"
include "hvdistr1i.mm"
include "cmul.mm"
include "neg1mulneg1e1.mm"
include "oveq1i.mm"
include "hvmulassi.mm"
include "chil.mm"
include "wcel.mm"
include "wceq.mm"
include "ax-hvmulid.mm"
include "ax-mp.mm"
include "3eqtr3i.mm"
include "hvcomi.mm"
include "3eqtr4i.mm"
include "3eqtri.mm"

theorem hvnegdii
  let cA: class A
  let cB: class B
  assume hvnegdi.1: |- A e. ~H
  assume hvnegdi.2: |- B e. ~H


  assert |- ( -u 1 .h ( A -h B ) ) = ( B -h A )

  proof
    c1
    cneg
    #
    cA
    cB
    cmv
    co
    #
    csm
    co
    @0
    cA
    @0
    cB
    csm
    co
    #
    cva
    co
    #
    csm
    co
    @0
    cA
    csm
    co
    #
    @0
    @2
    csm
    co
    #
    cva
    co
    #
    cB
    cA
    cmv
    co
    #
    @1
    @3
    @0
    csm
    cA
    cB
    hvnegdi.1
    hvnegdi.2
    hvsubvali
    oveq2i
    @0
    cA
    @2
    neg1cn
    hvnegdi.1
    @0
    cB
    neg1cn
    hvnegdi.2
    hvmulcli
    #
    hvdistr1i
    @5
    @4
    cva
    co
    cB
    @4
    cva
    co
    @6
    @7
    @5
    cB
    @4
    cva
    @0
    @0
    cmul
    co
    #
    cB
    csm
    co
    c1
    cB
    csm
    co
    #
    @5
    cB
    @9
    c1
    cB
    csm
    neg1mulneg1e1
    oveq1i
    @0
    @0
    cB
    neg1cn
    neg1cn
    hvnegdi.2
    hvmulassi
    cB
    chil
    wcel
    @10
    cB
    wceq
    hvnegdi.2
    cB
    ax-hvmulid
    ax-mp
    3eqtr3i
    oveq1i
    @4
    @5
    @0
    cA
    neg1cn
    hvnegdi.1
    hvmulcli
    @0
    @2
    neg1cn
    @8
    hvmulcli
    hvcomi
    cB
    cA
    hvnegdi.2
    hvnegdi.1
    hvsubvali
    3eqtr4i
    3eqtri
end
