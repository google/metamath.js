include "c0v.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cc0.mm"
include "chil.mm"
include "wcel.mm"
include "cc.mm"
include "ax-hv0cl.mm"
include "lnfnfi.mm"
include "ffvelrni.mm"
include "ax-mp.mm"
include "pncan3oi.mm"
include "c1.mm"
include "cmul.mm"
include "csm.mm"
include "cva.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "lnfnli.mm"
include "mp3an.mm"
include "hvmulcli.mm"
include "ax-hvaddid.mm"
include "ax-hvmulid.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "eqtr3i.mm"
include "mulid2i.mm"
include "oveq1i.mm"
include "subidi.mm"

theorem lnfn0i
  let cT: class T
  assume lnfnl.1: |- T e. LinFn


  assert |- ( T ` 0h ) = 0

  proof
    c0v
    cT
    cfv
    #
    @0
    caddc
    co
    #
    @0
    cmin
    co
    #
    @0
    cc0
    @0
    @0
    c0v
    chil
    wcel
    #
    @0
    cc
    wcel
    ax-hv0cl
    chil
    cc
    c0v
    cT
    cT
    lnfnl.1
    lnfnfi
    ffvelrni
    ax-mp
    #
    @4
    pncan3oi
    @0
    @0
    cmin
    co
    @2
    cc0
    @0
    @1
    @0
    cmin
    c1
    @0
    cmul
    co
    #
    @0
    caddc
    co
    #
    @0
    @1
    c1
    c0v
    csm
    co
    #
    c0v
    cva
    co
    #
    cT
    cfv
    #
    @6
    @0
    c1
    cc
    wcel
    @3
    @3
    @9
    @6
    wceq
    ax-1cn
    ax-hv0cl
    ax-hv0cl
    c1
    c0v
    c0v
    cT
    lnfnl.1
    lnfnli
    mp3an
    @8
    c0v
    cT
    @8
    @7
    c0v
    @7
    chil
    wcel
    @8
    @7
    wceq
    c1
    c0v
    ax-1cn
    ax-hv0cl
    hvmulcli
    @7
    ax-hvaddid
    ax-mp
    @3
    @7
    c0v
    wceq
    ax-hv0cl
    c0v
    ax-hvmulid
    ax-mp
    eqtri
    fveq2i
    eqtr3i
    @5
    @0
    @0
    caddc
    @0
    @4
    mulid2i
    oveq1i
    eqtr3i
    oveq1i
    @0
    @4
    subidi
    eqtr3i
    eqtr3i
end
