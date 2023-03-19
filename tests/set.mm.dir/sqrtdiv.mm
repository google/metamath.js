include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "crp.mm"
include "cdiv.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "cmul.mm"
include "rerpdivcl.mm"
include "adantlr.mm"
include "clt.mm"
include "elrp.mm"
include "divge0.mm"
include "sylan2b.mm"
include "resqrtcl.mm"
include "syl2anc.mm"
include "recnd.mm"
include "rpsqrtcl.mm"
include "adantl.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "divcan4d.mm"
include "wceq.mm"
include "rprege0.mm"
include "sqrtmul.mm"
include "syl21anc.mm"
include "simpll.mm"
include "cc.mm"
include "rpcn.mm"
include "wne.mm"
include "rpne0.mm"
include "divcan1d.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "oveq1d.mm"

theorem sqrtdiv
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ 0 <_ A ) /\ B e. RR+ ) -> ( sqrt ` ( A / B ) ) = ( ( sqrt ` A ) / ( sqrt ` B ) ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cB
    crp
    wcel
    #
    wa
    #
    cA
    cB
    cdiv
    co
    #
    csqrt
    cfv
    #
    cB
    csqrt
    cfv
    #
    cmul
    co
    #
    @7
    cdiv
    co
    @6
    cA
    csqrt
    cfv
    #
    @7
    cdiv
    co
    @4
    @6
    @7
    @4
    @6
    @4
    @5
    cr
    wcel
    #
    cc0
    @5
    cle
    wbr
    #
    @6
    cr
    wcel
    @0
    @3
    @10
    @1
    cA
    cB
    rerpdivcl
    adantlr
    #
    @3
    @2
    cB
    cr
    wcel
    #
    cc0
    cB
    clt
    wbr
    wa
    @11
    cB
    elrp
    cA
    cB
    divge0
    sylan2b
    #
    @5
    resqrtcl
    syl2anc
    recnd
    @4
    @7
    @3
    @7
    crp
    wcel
    @2
    cB
    rpsqrtcl
    adantl
    #
    rpcnd
    @4
    @7
    @15
    rpne0d
    divcan4d
    @4
    @8
    @9
    @7
    cdiv
    @4
    @5
    cB
    cmul
    co
    #
    csqrt
    cfv
    #
    @8
    @9
    @4
    @10
    @11
    @13
    cc0
    cB
    cle
    wbr
    wa
    #
    @17
    @8
    wceq
    @12
    @14
    @3
    @18
    @2
    cB
    rprege0
    adantl
    @5
    cB
    sqrtmul
    syl21anc
    @4
    @16
    cA
    csqrt
    @4
    cA
    cB
    @4
    cA
    @0
    @1
    @3
    simpll
    recnd
    @3
    cB
    cc
    wcel
    @2
    cB
    rpcn
    adantl
    @3
    cB
    cc0
    wne
    @2
    cB
    rpne0
    adantl
    divcan1d
    fveq2d
    eqtr3d
    oveq1d
    eqtr3d
end
