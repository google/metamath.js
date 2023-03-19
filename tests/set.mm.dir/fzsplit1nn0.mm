include "cn0.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "caddc.mm"
include "cun.mm"
include "wceq.mm"
include "cn.mm"
include "cc0.mm"
include "wo.mm"
include "wa.mm"
include "wi.mm"
include "elnn0.mm"
include "nnge1.mm"
include "adantr.mm"
include "simprr.mm"
include "cz.mm"
include "wb.mm"
include "nnz.mm"
include "1zzd.mm"
include "nn0z.mm"
include "ad2antrl.mm"
include "elfz.mm"
include "syl3anc.mm"
include "mpbir2and.mm"
include "fzsplit.mm"
include "syl.mm"
include "uncom.mm"
include "c0.mm"
include "oveq1.mm"
include "0p1e1.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "oveq2.mm"
include "fz10.mm"
include "uneq12d.mm"
include "un0.mm"
include "syl5req.mm"
include "jaoian.mm"
include "ex.mm"
include "sylbi.mm"
include "3impib.mm"

theorem fzsplit1nn0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. NN0 /\ B e. NN0 /\ A <_ B ) -> ( 1 ... B ) = ( ( 1 ... A ) u. ( ( A + 1 ) ... B ) ) )

  proof
    cA
    cn0
    wcel
    #
    cB
    cn0
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    c1
    cB
    cfz
    co
    #
    c1
    cA
    cfz
    co
    #
    cA
    c1
    caddc
    co
    #
    cB
    cfz
    co
    #
    cun
    #
    wceq
    #
    @0
    cA
    cn
    wcel
    #
    cA
    cc0
    wceq
    #
    wo
    #
    @1
    @2
    wa
    #
    @8
    wi
    cA
    elnn0
    @11
    @12
    @8
    @9
    @12
    @8
    @10
    @9
    @12
    wa
    #
    cA
    @3
    wcel
    #
    @8
    @13
    @14
    c1
    cA
    cle
    wbr
    #
    @2
    @9
    @15
    @12
    cA
    nnge1
    adantr
    @9
    @1
    @2
    simprr
    @13
    cA
    cz
    wcel
    #
    c1
    cz
    wcel
    cB
    cz
    wcel
    #
    @14
    @15
    @2
    wa
    wb
    @9
    @16
    @12
    cA
    nnz
    adantr
    @13
    1zzd
    @1
    @17
    @9
    @2
    cB
    nn0z
    ad2antrl
    cA
    c1
    cB
    elfz
    syl3anc
    mpbir2and
    cA
    c1
    cB
    fzsplit
    syl
    @10
    @12
    wa
    #
    @7
    @6
    @4
    cun
    #
    @3
    @4
    @6
    uncom
    @18
    @19
    @3
    c0
    cun
    @3
    @18
    @6
    @3
    @4
    c0
    @18
    @5
    c1
    cB
    cfz
    @18
    @5
    cc0
    c1
    caddc
    co
    #
    c1
    @10
    @5
    @20
    wceq
    @12
    cA
    cc0
    c1
    caddc
    oveq1
    adantr
    0p1e1
    syl6eq
    oveq1d
    @18
    @4
    c1
    cc0
    cfz
    co
    #
    c0
    @10
    @4
    @21
    wceq
    @12
    cA
    cc0
    c1
    cfz
    oveq2
    adantr
    fz10
    syl6eq
    uneq12d
    @3
    un0
    syl6eq
    syl5req
    jaoian
    ex
    sylbi
    3impib
end
