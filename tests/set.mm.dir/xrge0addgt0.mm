include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cxad.mm"
include "wceq.mm"
include "cxr.mm"
include "0xr.mm"
include "xaddid1.mm"
include "ax-mp.mm"
include "simplr.mm"
include "simpr.mm"
include "wi.mm"
include "a1i.mm"
include "iccssxr.mm"
include "simplll.mm"
include "sseldi.mm"
include "simpllr.mm"
include "xlt2add.mm"
include "syl22anc.mm"
include "mp2and.mm"
include "syl5eqbrr.mm"
include "oveq2.mm"
include "adantl.mm"
include "breq2d.mm"
include "syl.mm"
include "bitr3d.mm"
include "mpbird.mm"
include "cle.mm"
include "wo.mm"
include "pnfxr.mm"
include "iccgelb.mm"
include "syl3anc.mm"
include "xrleloe.mm"
include "biimpa.mm"
include "syl21anc.mm"
include "mpjaodan.mm"

theorem xrge0addgt0
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. ( 0 [,] +oo ) /\ B e. ( 0 [,] +oo ) ) /\ 0 < A ) -> 0 < ( A +e B ) )

  proof
    cA
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cc0
    cA
    clt
    wbr
    #
    wa
    #
    cc0
    cB
    clt
    wbr
    #
    cc0
    cA
    cB
    cxad
    co
    #
    clt
    wbr
    #
    cc0
    cB
    wceq
    #
    @5
    @6
    wa
    #
    cc0
    cc0
    cc0
    cxad
    co
    #
    @7
    clt
    cc0
    cxr
    wcel
    #
    @11
    cc0
    wceq
    0xr
    cc0
    xaddid1
    ax-mp
    @10
    @4
    @6
    @11
    @7
    clt
    wbr
    #
    @3
    @4
    @6
    simplr
    @5
    @6
    simpr
    @10
    @12
    @12
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @4
    @6
    wa
    @13
    wi
    @12
    @10
    0xr
    a1i
    #
    @16
    @10
    @0
    cxr
    cA
    cc0
    cpnf
    iccssxr
    #
    @1
    @2
    @4
    @6
    simplll
    sseldi
    @10
    @0
    cxr
    cB
    @17
    @1
    @2
    @4
    @6
    simpllr
    sseldi
    cc0
    cc0
    cA
    cB
    xlt2add
    syl22anc
    mp2and
    syl5eqbrr
    @5
    @9
    wa
    #
    @8
    @4
    @3
    @4
    @9
    simplr
    @18
    cc0
    cA
    cc0
    cxad
    co
    #
    clt
    wbr
    @8
    @4
    @18
    @19
    @7
    cc0
    clt
    @9
    @19
    @7
    wceq
    @5
    cc0
    cB
    cA
    cxad
    oveq2
    adantl
    breq2d
    @18
    @19
    cA
    cc0
    clt
    @18
    @14
    @19
    cA
    wceq
    @18
    @0
    cxr
    cA
    @17
    @1
    @2
    @4
    @9
    simplll
    sseldi
    cA
    xaddid1
    syl
    breq2d
    bitr3d
    mpbird
    @5
    @12
    @15
    cc0
    cB
    cle
    wbr
    #
    @6
    @9
    wo
    #
    @12
    @5
    0xr
    a1i
    #
    @5
    @0
    cxr
    cB
    @17
    @1
    @2
    @4
    simplr
    #
    sseldi
    @5
    @12
    cpnf
    cxr
    wcel
    #
    @2
    @20
    @22
    @24
    @5
    pnfxr
    a1i
    @23
    cc0
    cpnf
    cB
    iccgelb
    syl3anc
    @12
    @15
    wa
    @20
    @21
    cc0
    cB
    xrleloe
    biimpa
    syl21anc
    mpjaodan
end
