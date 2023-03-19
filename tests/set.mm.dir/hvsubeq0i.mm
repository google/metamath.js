include "cmv.mm"
include "co.mm"
include "c0v.mm"
include "wceq.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "cva.mm"
include "hvsubvali.mm"
include "eqeq1i.mm"
include "oveq1.mm"
include "sylbi.mm"
include "neg1cn.mm"
include "hvmulcli.mm"
include "hvadd32i.mm"
include "hvassi.mm"
include "hvnegidi.mm"
include "oveq2i.mm"
include "chil.mm"
include "wcel.mm"
include "ax-hvaddid.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "hvaddid2i.mm"
include "3eqtr3g.mm"
include "hvsubid.mm"
include "syl6eq.mm"
include "impbii.mm"

theorem hvsubeq0i
  let cA: class A
  let cB: class B
  assume hvnegdi.1: |- A e. ~H
  assume hvnegdi.2: |- B e. ~H


  assert |- ( ( A -h B ) = 0h <-> A = B )

  proof
    cA
    cB
    cmv
    co
    #
    c0v
    wceq
    #
    cA
    cB
    wceq
    #
    @1
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
    cB
    cva
    co
    #
    c0v
    cB
    cva
    co
    #
    cA
    cB
    @1
    @5
    c0v
    wceq
    @6
    @7
    wceq
    @0
    @5
    c0v
    cA
    cB
    hvnegdi.1
    hvnegdi.2
    hvsubvali
    eqeq1i
    @5
    c0v
    cB
    cva
    oveq1
    sylbi
    @6
    cA
    cB
    cva
    co
    @4
    cva
    co
    #
    cA
    cA
    @4
    cB
    hvnegdi.1
    @3
    cB
    neg1cn
    hvnegdi.2
    hvmulcli
    #
    hvnegdi.2
    hvadd32i
    @8
    cA
    cB
    @4
    cva
    co
    #
    cva
    co
    #
    cA
    cA
    cB
    @4
    hvnegdi.1
    hvnegdi.2
    @9
    hvassi
    @11
    cA
    c0v
    cva
    co
    #
    cA
    @10
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
    @12
    cA
    wceq
    hvnegdi.1
    cA
    ax-hvaddid
    ax-mp
    eqtri
    eqtri
    eqtri
    cB
    hvnegdi.2
    hvaddid2i
    3eqtr3g
    @2
    @0
    cB
    cB
    cmv
    co
    #
    c0v
    cA
    cB
    cB
    cmv
    oveq1
    cB
    chil
    wcel
    @13
    c0v
    wceq
    hvnegdi.2
    cB
    hvsubid
    ax-mp
    syl6eq
    impbii
end
