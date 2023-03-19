include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "ce.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "cmul.mm"
include "cneg.mm"
include "caddc.mm"
include "cmin.mm"
include "wceq.mm"
include "cc0.mm"
include "wne.mm"
include "efcl.mm"
include "efne0.mm"
include "divrec.mm"
include "syl3an.mm"
include "3anidm23.mm"
include "efcan.mm"
include "eqcomd.mm"
include "wb.mm"
include "negcl.mm"
include "syl.mm"
include "ax-1cn.mm"
include "divmul2.mm"
include "mp3an1.mm"
include "syl12anc.mm"
include "mpbird.mm"
include "oveq2d.mm"
include "adantl.mm"
include "efadd.mm"
include "sylan2.mm"
include "eqtr4d.mm"
include "negsub.mm"
include "fveq2d.mm"
include "3eqtrrd.mm"

theorem efsub
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( exp ` ( A - B ) ) = ( ( exp ` A ) / ( exp ` B ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    ce
    cfv
    #
    cB
    ce
    cfv
    #
    cdiv
    co
    #
    @3
    c1
    @4
    cdiv
    co
    #
    cmul
    co
    #
    cA
    cB
    cneg
    #
    caddc
    co
    #
    ce
    cfv
    #
    cA
    cB
    cmin
    co
    #
    ce
    cfv
    @0
    @1
    @5
    @7
    wceq
    #
    @0
    @3
    cc
    wcel
    @1
    @4
    cc
    wcel
    #
    @1
    @4
    cc0
    wne
    #
    @12
    cA
    efcl
    cB
    efcl
    #
    cB
    efne0
    #
    @3
    @4
    divrec
    syl3an
    3anidm23
    @2
    @7
    @3
    @8
    ce
    cfv
    #
    cmul
    co
    #
    @10
    @1
    @7
    @18
    wceq
    @0
    @1
    @6
    @17
    @3
    cmul
    @1
    @6
    @17
    wceq
    #
    c1
    @4
    @17
    cmul
    co
    #
    wceq
    #
    @1
    @20
    c1
    cB
    efcan
    eqcomd
    @1
    @17
    cc
    wcel
    #
    @13
    @14
    @19
    @21
    wb
    #
    @1
    @8
    cc
    wcel
    #
    @22
    cB
    negcl
    #
    @8
    efcl
    syl
    @15
    @16
    c1
    cc
    wcel
    @22
    @13
    @14
    wa
    @23
    ax-1cn
    c1
    @17
    @4
    divmul2
    mp3an1
    syl12anc
    mpbird
    oveq2d
    adantl
    @1
    @0
    @24
    @10
    @18
    wceq
    @25
    cA
    @8
    efadd
    sylan2
    eqtr4d
    @2
    @9
    @11
    ce
    cA
    cB
    negsub
    fveq2d
    3eqtrrd
end
