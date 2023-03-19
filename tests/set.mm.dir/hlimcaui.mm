include "chli.mm"
include "wbr.mm"
include "cdm.mm"
include "ccau.mm"
include "cva.mm"
include "csm.mm"
include "cop.mm"
include "cno.mm"
include "cims.mm"
include "cfv.mm"
include "cca.mm"
include "chil.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "cin.mm"
include "cmopn.mm"
include "clm.mm"
include "wss.mm"
include "cres.mm"
include "eqid.mm"
include "hhlm.mm"
include "resss.mm"
include "eqsstri.mm"
include "dmss.mm"
include "ax-mp.mm"
include "cxmt.mm"
include "wcel.mm"
include "hhxmet.mm"
include "lmcau.mm"
include "sstri.mm"
include "dmeqi.mm"
include "dmres.mm"
include "eqtri.mm"
include "inss1.mm"
include "ssini.mm"
include "hhcau.mm"
include "sseqtr4i.mm"
include "wrel.mm"
include "relres.mm"
include "releqi.mm"
include "mpbir.mm"
include "releldmi.mm"
include "sseldi.mm"

theorem hlimcaui
  let cA: class A
  let cF: class F


  assert |- ( F ~~>v A -> F e. Cauchy )

  proof
    cF
    cA
    chli
    wbr
    chli
    cdm
    #
    ccau
    cF
    @0
    cva
    csm
    cop
    cno
    cop
    #
    cims
    cfv
    #
    cca
    cfv
    #
    chil
    cn
    cmap
    co
    #
    cin
    ccau
    @0
    @3
    @4
    @0
    @2
    cmopn
    cfv
    #
    clm
    cfv
    #
    cdm
    #
    @3
    chli
    @6
    wss
    @0
    @7
    wss
    chli
    @6
    @4
    cres
    #
    @6
    @2
    @1
    @5
    @1
    eqid
    #
    @2
    eqid
    #
    @5
    eqid
    #
    hhlm
    #
    @6
    @4
    resss
    eqsstri
    chli
    @6
    dmss
    ax-mp
    @2
    chil
    cxmt
    cfv
    wcel
    @7
    @3
    wss
    @2
    @1
    @9
    @10
    hhxmet
    @2
    @5
    chil
    @11
    lmcau
    ax-mp
    sstri
    @0
    @4
    @7
    cin
    #
    @4
    @0
    @8
    cdm
    @13
    chli
    @8
    @12
    dmeqi
    @6
    @4
    dmres
    eqtri
    @4
    @7
    inss1
    eqsstri
    ssini
    @2
    @1
    @9
    @10
    hhcau
    sseqtr4i
    cF
    cA
    chli
    chli
    wrel
    @8
    wrel
    @6
    @4
    relres
    chli
    @8
    @12
    releqi
    mpbir
    releldmi
    sseldi
end
