include "clo.mm"
include "wcel.mm"
include "c0v.mm"
include "cfv.mm"
include "cmv.mm"
include "co.mm"
include "cva.mm"
include "c1.mm"
include "csm.mm"
include "chil.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "ax-hv0cl.mm"
include "hvmulcli.mm"
include "ax-hvaddid.mm"
include "ax-mp.mm"
include "ax-hvmulid.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "cc.mm"
include "wa.mm"
include "lnopl.mm"
include "mpanr12.mm"
include "mpan2.mm"
include "syl5eqr.mm"
include "wf.mm"
include "lnopf.mm"
include "ffvelrn.mm"
include "syl.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "hvsubid.mm"
include "hvpncan.mm"
include "anidms.mm"
include "3eqtr3rd.mm"

theorem lnop0
  let cT: class T


  assert |- ( T e. LinOp -> ( T ` 0h ) = 0h )

  proof
    cT
    clo
    wcel
    #
    c0v
    cT
    cfv
    #
    @1
    cmv
    co
    #
    @1
    @1
    cva
    co
    #
    @1
    cmv
    co
    #
    c0v
    @1
    @0
    @1
    @3
    @1
    cmv
    @0
    @1
    c1
    @1
    csm
    co
    #
    @1
    cva
    co
    #
    @3
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
    c0v
    chil
    wcel
    #
    @7
    c0v
    wceq
    ax-hv0cl
    c0v
    ax-hvmulid
    ax-mp
    eqtri
    fveq2i
    @0
    c1
    cc
    wcel
    #
    @9
    @6
    wceq
    #
    ax-1cn
    @0
    @11
    wa
    @10
    @10
    @12
    ax-hv0cl
    ax-hv0cl
    c1
    c0v
    c0v
    cT
    lnopl
    mpanr12
    mpan2
    syl5eqr
    @0
    @5
    @1
    @1
    cva
    @0
    @1
    chil
    wcel
    #
    @5
    @1
    wceq
    @0
    chil
    chil
    cT
    wf
    #
    @13
    cT
    lnopf
    @14
    @10
    @13
    ax-hv0cl
    chil
    chil
    c0v
    cT
    ffvelrn
    mpan2
    syl
    #
    @1
    ax-hvmulid
    syl
    oveq1d
    eqtrd
    oveq1d
    @0
    @13
    @2
    c0v
    wceq
    @15
    @1
    hvsubid
    syl
    @0
    @13
    @4
    @1
    wceq
    #
    @15
    @13
    @16
    @1
    @1
    hvpncan
    anidms
    syl
    3eqtr3rd
end
